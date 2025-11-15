use super::read::WholeRwLockReadGuard;
use crate::core::Allocation;
use std::{
    fmt::{self, Debug, Display},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut, Drop},
    ptr::NonNull,
    thread,
};

/// RAII structure used to release the exclusive global write access of a lock when
/// dropped.
///
/// This structure is created by the [`write`] and [`try_write`] methods on
/// [`WholeRwLock`].
///
/// [`WholeRwLock`]: super::lock::WholeRwLock
/// [`write`]: super::lock::WholeRwLock::write
/// [`try_write`]: super::lock::WholeRwLock::try_write
#[must_use = "if unused the WholeRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct WholeRwLockWriteGuard<'a, T: ?Sized + 'a> {
    pub(super) allocation: NonNull<Allocation<T>>,
    pub(super) variance: PhantomData<&'a mut ()>,
    // For opting-out of `Send`.
    pub(super) phantom: PhantomData<*const ()>,
}

#[cfg(feature = "downgrade")]
impl<'a, T> WholeRwLockWriteGuard<'a, T> {
    /// Downgrades a subfield-write-locked `WholeRwLockWriteGuard` into a subfield-read-locked [`WholeRwLockReadGuard`].
    ///
    /// Since we have the `WholeRwLockWriteGuard`, the [`WholeRwLock`] must already be locked for writing, so
    /// this method cannot fail.
    ///
    /// After downgrading, other readers and writers will be allowed to access the protected data.
    ///
    /// [`WholeRwLockReadGuard`]: super::read::WholeRwLockReadGuard
    /// [`WholeRwLock`]: super::lock::WholeRwLock
    pub fn downgrade(s: Self) -> WholeRwLockReadGuard<'a, T> {
        let allocation = s.allocation;
        mem::forget(s);
        unsafe {
            // SAFETY: By construction `allocation` points to live and valid data.
            Allocation::get_metadata_disjoint(allocation)
                .lock
                // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
                //         The existance of `s` guarantees that the counter is at least 1.
                .downgrade_global_writer_unchecked()
        };
        WholeRwLockReadGuard {
            allocation,
            variance: PhantomData,
            phantom: PhantomData,
        }
    }
}

impl<T> Deref for WholeRwLockWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        //         Aliasing rules are upheld via synchronization.
        unsafe { Allocation::get_data_ref_disjoint(self.allocation) }
    }
}

impl<T> DerefMut for WholeRwLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        //         Aliasing rules are upheld via by synchronization.
        unsafe { Allocation::get_data_mut_disjoint(self.allocation) }
    }
}

impl<T: ?Sized> Drop for WholeRwLockWriteGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: By construction `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        if thread::panicking() {
            metadata.state.poison();
        }
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        //         The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            metadata.lock.drop_global_writer_unchecked();
        }
    }
}

impl<T: Debug> Debug for WholeRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: Display> Display for WholeRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for WholeRwLockWriteGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::WholeRwLockWriteGuard;
    use crate::core::{Allocation, Metadata};
    use std::{
        fmt::{self, Debug, Display},
        marker::PhantomData,
        mem,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    /// RAII structure used to release the exclusive global write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`WholeRwLockWriteGuard`].
    ///
    /// [`map`]: super::WholeRwLockWriteGuard::map
    /// [`filter_map`]: super::WholeRwLockWriteGuard::filter_map
    #[must_use = "if unused the WholeRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedWholeRwLockWriteGuard<'a, T: ?Sized + 'a> {
        metadata: &'a Metadata,
        data: NonNull<T>,
        phantom: PhantomData<*const ()>, // For opting-out of `Send`.
    }

    impl<'a, T> WholeRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedWholeRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `WholeRwLock` is already locked writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `WholeRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `WholeRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedWholeRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.allocation);
                // SAFETY: By construction `allocation` points to live and valid data.
                //         Aliasing rules are upheld via synchronization.
                let data = NonNull::from_mut(f(Allocation::get_data_mut_disjoint(orig.allocation)));
                mem::forget(orig);
                MappedWholeRwLockWriteGuard {
                    metadata,
                    data,
                    phantom: PhantomData,
                }
            }
        }

        /// Makes a [`MappedWholeRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `WholeRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `WholeRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `WholeRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedWholeRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.allocation);
                // SAFETY: By construction `allocation` points to live and valid data.
                //         Aliasing rules are upheld via synchronization.
                let data = f(Allocation::get_data_mut_disjoint(orig.allocation));
                match data {
                    Some(data) => {
                        mem::forget(orig);
                        Ok(MappedWholeRwLockWriteGuard {
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

    impl<'a, T: ?Sized> MappedWholeRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedWholeRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `WholeRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedWholeRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedWholeRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedWholeRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let metadata = orig.metadata;
            mem::forget(orig);
            MappedWholeRwLockWriteGuard {
                metadata,
                data,
                phantom: PhantomData,
            }
        }

        /// Makes a [`MappedWholeRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `WholeRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedWholeRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedWholeRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedWholeRwLockWriteGuard<'a, U>, Self>
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
                    Ok(MappedWholeRwLockWriteGuard {
                        metadata,
                        data: NonNull::from_mut(data),
                        phantom: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<T: ?Sized> Deref for MappedWholeRwLockWriteGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_ref() }
        }
    }

    impl<T: ?Sized> DerefMut for MappedWholeRwLockWriteGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_mut() }
        }
    }

    impl<T: ?Sized> Drop for MappedWholeRwLockWriteGuard<'_, T> {
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

    impl<T: Debug + ?Sized> Debug for MappedWholeRwLockWriteGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<T: Display + ?Sized> Display for MappedWholeRwLockWriteGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedWholeRwLockWriteGuard<'_, T> {}
}
