use crate::core::Allocation;
use std::{
    fmt::{self, Debug, Display},
    marker::PhantomData,
    ops::{Deref, Drop},
    ptr::NonNull,
};

/// RAII structure used to release the shared global read access of a lock when
/// dropped.
///
/// This structure is created by the [`read`] and [`try_read`] methods on
/// [`WholeRwLock`].
///
/// [`WholeRwLock`]: super::lock::WholeRwLock
/// [`read`]: super::lock::WholeRwLock::read
/// [`try_read`]: super::lock::WholeRwLock::try_read
#[must_use = "if unused the WholeRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct WholeRwLockReadGuard<'a, T: ?Sized + 'a> {
    pub(super) allocation: NonNull<Allocation<T>>,
    pub(super) variance: PhantomData<&'a T>,
}

impl<T: ?Sized> Deref for WholeRwLockReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: - By construction, `allocation` points to live and valid data.
        //         - Aliasing rules are upheld via synchronization.
        unsafe { Allocation::get_data_ref_disjoint(self.allocation) }
    }
}

impl<T: ?Sized> Drop for WholeRwLockReadGuard<'_, T> {
    fn drop(&mut self) {
        unsafe {
            // SAFETY: By construction, `allocation` points to live and valid data.
            Allocation::get_metadata_disjoint(self.allocation)
                .lock
                // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
                //         The existance of `self` guarantees that the counter is at least 1.
                .drop_global_reader_unchecked();
        }
    }
}

impl<T: ?Sized + Debug> Debug for WholeRwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized + Display> Display for WholeRwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: ?Sized + Sync> Sync for WholeRwLockReadGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::WholeRwLockReadGuard;
    use crate::core::{Allocation, Metadata};
    use std::{
        fmt::{self, Debug, Display},
        marker::PhantomData,
        mem,
        ops::{Deref, Drop},
    };

    /// RAII structure used to release the shared global read access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`WholeRwLockReadGuard`].
    ///
    /// [`map`]: super::WholeRwLockReadGuard::map
    /// [`filter_map`]: super::WholeRwLockReadGuard::filter_map
    #[must_use = "if unused the WholeRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedWholeRwLockReadGuard<'a, T: ?Sized + 'a> {
        metadata: &'a Metadata,
        data: &'a T,
        phantom: PhantomData<*const ()>, // For opting-out of `Send`.
    }

    impl<'a, T: ?Sized> WholeRwLockReadGuard<'a, T> {
        /// Makes a [`MappedWholeRwLockReadGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `WholeRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `WholeRwLockReadGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `WholeRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedWholeRwLockReadGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction, `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.allocation);
                // SAFETY: - By construction, `allocation` points to live and valid data.
                //         - Aliasing rules are upheld via synchronization.
                let data = f(Allocation::get_data_ref_disjoint(orig.allocation));
                mem::forget(orig);
                MappedWholeRwLockReadGuard {
                    metadata,
                    data,
                    phantom: PhantomData,
                }
            }
        }

        /// Makes a [`MappedWholeRwLockReadGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `WholeRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `WholeRwLockReadGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `WholeRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedWholeRwLockReadGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction, `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.allocation);
                // SAFETY: - By construction, `allocation` points to live and valid data.
                //         - Aliasing rules are upheld via synchronization.
                let data = f(Allocation::get_data_ref_disjoint(orig.allocation));
                match data {
                    Some(data) => {
                        mem::forget(orig);
                        Ok(MappedWholeRwLockReadGuard {
                            metadata,
                            data,
                            phantom: PhantomData,
                        })
                    }
                    None => Err(orig),
                }
            }
        }
    }

    impl<'a, T: ?Sized> MappedWholeRwLockReadGuard<'a, T> {
        /// Makes a [`MappedWholeRwLockReadGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `WholeRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedWholeRwLockReadGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedWholeRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedWholeRwLockReadGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            let data = f(orig.data);
            let metadata = orig.metadata;
            mem::forget(orig);
            MappedWholeRwLockReadGuard {
                metadata,
                data,
                phantom: PhantomData,
            }
        }

        /// Makes a [`MappedWholeRwLockReadGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `WholeRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedWholeRwLockReadGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedWholeRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the WholeRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedWholeRwLockReadGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            let data = f(orig.data);
            match data {
                Some(data) => {
                    let metadata = orig.metadata;
                    mem::forget(orig);
                    Ok(MappedWholeRwLockReadGuard {
                        metadata,
                        data,
                        phantom: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<T: ?Sized> Deref for MappedWholeRwLockReadGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            self.data
        }
    }

    impl<T: ?Sized> Drop for MappedWholeRwLockReadGuard<'_, T> {
        fn drop(&mut self) {
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            //         The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.metadata.lock.drop_global_reader_unchecked();
            }
        }
    }

    impl<T: Debug + ?Sized> Debug for MappedWholeRwLockReadGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<T: Display + ?Sized> Display for MappedWholeRwLockReadGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<T: Sync + ?Sized> Sync for MappedWholeRwLockReadGuard<'_, T> {}
}
