use super::{lock::InnerElementRwLock, read::ElementRwLockReadGuard};
use crate::core::Allocation;
use std::{
    fmt::{self, Debug, Display},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut, Drop},
    thread,
};

/// RAII structure used to release the exclusive subfield write access of a lock when
/// dropped.
///
/// This structure is created by the [`write`] and [`try_write`] methods on
/// [`ElementRwLock`].
///
/// [`ElementRwLock`]: super::lock::ElementRwLock
/// [`write`]: super::lock::ElementRwLock::write
/// [`try_write`]: super::lock::ElementRwLock::try_write
#[must_use = "if unused the ElementRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ElementRwLockWriteGuard<'a, T> {
    pub(super) lock: &'a InnerElementRwLock<T>,
    pub(super) variance: PhantomData<&'a ()>,
    // For opting-out of `Send`.
    pub(super) phantom: PhantomData<*const ()>,
}

#[cfg(feature = "downgrade")]
impl<'a, T> ElementRwLockWriteGuard<'a, T> {
    /// Downgrades a subfield-write-locked `ElementRwLockWriteGuard` into a subfield-read-locked [`ElementRwLockReadGuard`].
    ///
    /// Since we have the `ElementRwLockWriteGuard`, the [`ElementRwLock`] must already be locked for writing, so
    /// this method cannot fail.
    ///
    /// After downgrading, if this was the only write guard, global readers will be allowed to read the protected data.
    ///
    /// [`ElementRwLockReadGuard`]: super::read::ElementRwLockReadGuard
    /// [`ElementRwLock`]: super::lock::ElementRwLock
    pub fn downgrade(s: Self) -> ElementRwLockReadGuard<'a, T> {
        let lock = s.lock;
        mem::forget(s);
        unsafe {
            // SAFETY: By construction, `allocation` points to live and valid data.
            Allocation::get_metadata_disjoint(lock.allocation)
                .lock
                // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
                //         The existance of `s` guarantees that the counter is at least 1.
                .downgrade_writer_unchecked()
        };
        ElementRwLockReadGuard { lock, phantom: PhantomData }
    }
}

impl<T> Deref for ElementRwLockWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: By construction, `allocation` points to live and valid data.
        //         Aliasing rules are upheld via synchronization.
        unsafe { Allocation::get_element_disjoint(self.lock.allocation, self.lock.index) }
    }
}

impl<T> DerefMut for ElementRwLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: By construction, `allocation` points to live and valid data.
        //         Aliasing rules are upheld via by synchronization.
        unsafe { Allocation::get_element_mut_disjoint(self.lock.allocation, self.lock.index) }
    }
}

impl<T> Drop for ElementRwLockWriteGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.lock.allocation) };
        if thread::panicking() {
            metadata.state.poison();
        }
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        //         The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            metadata.lock.drop_writer_unchecked();
        }
    }
}

impl<T: Debug> Debug for ElementRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: Display> Display for ElementRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for ElementRwLockWriteGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::ElementRwLockWriteGuard;
    use crate::core::{Allocation, Metadata};
    use std::{
        fmt::{self, Debug, Display},
        marker::PhantomData,
        mem,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    /// RAII structure used to release the exclusive subfield write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`ElementRwLockWriteGuard`].
    ///
    /// [`map`]: super::ElementRwLockWriteGuard::map
    /// [`filter_map`]: super::ElementRwLockWriteGuard::filter_map
    #[must_use = "if unused the ElementRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedElementRwLockWriteGuard<'a, T: ?Sized + 'a> {
        metadata: &'a Metadata,
        data: NonNull<T>,
        phantom: PhantomData<*const ()>, // For opting-out of `Send`.
    }

    impl<'a, T> ElementRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedElementRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwLock` is already locked writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ElementRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElementRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction, `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.lock.allocation);
                // SAFETY: By construction, `allocation` points to live and valid data.
                //         Aliasing rules are upheld via synchronization.
                let data = NonNull::from_mut(f(Allocation::get_element_mut_disjoint(orig.lock.allocation, orig.lock.index)));
                mem::forget(orig);
                MappedElementRwLockWriteGuard {
                    metadata,
                    data,
                    phantom: PhantomData,
                }
            }
        }

        /// Makes a [`MappedElementRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ElementRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElementRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction, `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.lock.allocation);
                // SAFETY: By construction, `allocation` points to live and valid data.
                //         Aliasing rules are upheld via synchronization.
                let data = f(Allocation::get_element_mut_disjoint(orig.lock.allocation, orig.lock.index));
                match data {
                    Some(data) => {
                        mem::forget(orig);
                        Ok(MappedElementRwLockWriteGuard {
                            metadata,
                            data: NonNull::from_mut(data),
                            phantom: PhantomData,
                        })
                    }
                    None => Err(orig),
                }
            }
        }
    }

    impl<'a, T: ?Sized> MappedElementRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedElementRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedElementRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedElementRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let metadata = orig.metadata;
            mem::forget(orig);
            MappedElementRwLockWriteGuard {
                metadata,
                data,
                phantom: PhantomData,
            }
        }

        /// Makes a [`MappedElementRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedElementRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedElementRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            let data = f(unsafe { orig.data.as_mut() });
            match data {
                Some(data) => {
                    let metadata = orig.metadata;
                    mem::forget(orig);
                    Ok(MappedElementRwLockWriteGuard {
                        metadata,
                        data: NonNull::from_mut(data),
                        phantom: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<T: ?Sized> Deref for MappedElementRwLockWriteGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_ref() }
        }
    }

    impl<T: ?Sized> DerefMut for MappedElementRwLockWriteGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_mut() }
        }
    }

    impl<T: ?Sized> Drop for MappedElementRwLockWriteGuard<'_, T> {
        fn drop(&mut self) {
            if thread::panicking() {
                self.metadata.state.poison();
            }
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            //         The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.metadata.lock.drop_writer_unchecked();
            }
        }
    }

    impl<T: Debug + ?Sized> Debug for MappedElementRwLockWriteGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<T: Display + ?Sized> Display for MappedElementRwLockWriteGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedElementRwLockWriteGuard<'_, T> {}
}
