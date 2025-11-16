use super::read::SubfieldRwLockReadGuard;
use crate::core::Metadata;
use std::{
    fmt::{self, Debug, Display},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut, Drop},
    ptr::NonNull,
    thread,
};

/// RAII structure used to release the exclusive subfield write access of a lock when
/// dropped.
///
/// This structure is created by the [`write`] and [`try_write`] methods on
/// [`SubfieldRwLock`].
///
/// [`SubfieldRwLock`]: super::lock::SubfieldRwLock
/// [`write`]: super::lock::SubfieldRwLock::write
/// [`try_write`]: super::lock::SubfieldRwLock::try_write
#[must_use = "if unused the SubfieldRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct SubfieldRwLockWriteGuard<'a, T: ?Sized + 'a> {
    pub(super) metadata: &'a Metadata,
    pub(super) data: NonNull<T>,
    pub(super) variance: PhantomData<&'a mut T>,
}

#[cfg(feature = "downgrade")]
impl<'a, T> SubfieldRwLockWriteGuard<'a, T> {
    /// Downgrades a subfield-write-locked `SubfieldRwLockWriteGuard` into a subfield-read-locked [`SubfieldRwLockReadGuard`].
    ///
    /// Since we have the `SubfieldRwLockWriteGuard`, the [`SubfieldRwLock`] must already be locked for writing, so
    /// this method cannot fail.
    ///
    /// After downgrading, other readers and writers will be allowed to access the protected data.
    ///
    /// [`SubfieldRwLockReadGuard`]: super::read::SubfieldRwLockReadGuard
    /// [`SubfieldRwLock`]: super::lock::SubfieldRwLock
    pub fn downgrade(s: Self) -> SubfieldRwLockReadGuard<'a, T> {
        let metadata = s.metadata;
        let data = s.data;
        mem::forget(s);
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        //         The existance of `s` guarantees that the counter is at least 1.
        unsafe {
            metadata.lock.downgrade_subfield_writer_unchecked();
        }
        SubfieldRwLockReadGuard {
            metadata,
            // SAFETY: - By construction, `data` points to live and valid data.
            //         - Aliasing rules are upheld via synchronization.
            data: unsafe { data.as_ref() },
            phantom: PhantomData,
        }
    }
}

impl<T> Deref for SubfieldRwLockWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: - By construction, `data` points to live and valid data.
        //         - Aliasing rules are upheld via synchronization.
        unsafe { self.data.as_ref() }
    }
}

impl<T> DerefMut for SubfieldRwLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: - By construction, `data` points to live and valid data.
        //         - Aliasing rules are upheld via by synchronization.
        unsafe { self.data.as_mut() }
    }
}

impl<T: ?Sized> Drop for SubfieldRwLockWriteGuard<'_, T> {
    fn drop(&mut self) {
        if thread::panicking() {
            self.metadata.state.poison();
        }
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        //         The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            self.metadata.lock.drop_subfield_writer_unchecked();
        }
    }
}

impl<T: Debug> Debug for SubfieldRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: Display> Display for SubfieldRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for SubfieldRwLockWriteGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::SubfieldRwLockWriteGuard;
    use crate::core::Metadata;
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
    /// on [`SubfieldRwLockWriteGuard`].
    ///
    /// [`map`]: super::SubfieldRwLockWriteGuard::map
    /// [`filter_map`]: super::SubfieldRwLockWriteGuard::filter_map
    #[must_use = "if unused the SubfieldRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedSubfieldRwLockWriteGuard<'a, T: ?Sized + 'a> {
        metadata: &'a Metadata,
        data: NonNull<T>,
        variance: PhantomData<&'a mut T>,
    }

    impl<'a, T> SubfieldRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedSubfieldRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SubfieldRwLock` is already locked writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SubfieldRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `SubfieldRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedSubfieldRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let metadata = orig.metadata;
            // SAFETY: - By construction, `data` points to live and valid data.
            //         - Aliasing rules are upheld via synchronization.
            let data = unsafe { NonNull::from_mut(f(orig.data.as_mut())) };
            mem::forget(orig);
            MappedSubfieldRwLockWriteGuard {
                metadata,
                data,
                variance: PhantomData,
            }
        }

        /// Makes a [`MappedSubfieldRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SubfieldRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SubfieldRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `SubfieldRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedSubfieldRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            let metadata = orig.metadata;
            // SAFETY: - By construction, `data` points to live and valid data.
            //         - Aliasing rules are upheld via synchronization.
            let data = unsafe { f(orig.data.as_mut()) };
            match data {
                Some(data) => {
                    mem::forget(orig);
                    Ok(MappedSubfieldRwLockWriteGuard {
                        metadata,
                        data: NonNull::from_mut(data),
                        variance: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> MappedSubfieldRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedSubfieldRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SubfieldRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSubfieldRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedSubfieldRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedSubfieldRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let metadata = orig.metadata;
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            mem::forget(orig);
            MappedSubfieldRwLockWriteGuard {
                metadata,
                data,
                variance: PhantomData,
            }
        }

        /// Makes a [`MappedSubfieldRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SubfieldRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSubfieldRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedSubfieldRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedSubfieldRwLockWriteGuard<'a, U>, Self>
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
                    Ok(MappedSubfieldRwLockWriteGuard {
                        metadata,
                        data: NonNull::from_mut(data),
                        variance: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<T: ?Sized> Deref for MappedSubfieldRwLockWriteGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_ref() }
        }
    }

    impl<T: ?Sized> DerefMut for MappedSubfieldRwLockWriteGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            //         guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_mut() }
        }
    }

    impl<T: ?Sized> Drop for MappedSubfieldRwLockWriteGuard<'_, T> {
        fn drop(&mut self) {
            if thread::panicking() {
                self.metadata.state.poison();
            }
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            //         The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.metadata.lock.drop_subfield_writer_unchecked();
            }
        }
    }

    impl<T: Debug + ?Sized> Debug for MappedSubfieldRwLockWriteGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<T: Display + ?Sized> Display for MappedSubfieldRwLockWriteGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedSubfieldRwLockWriteGuard<'_, T> {}
}
