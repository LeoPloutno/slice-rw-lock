use crate::core::Metadata;
use std::{
    fmt::{self, Debug, Display},
    marker::PhantomData,
    ops::{Deref, Drop},
};

/// RAII structure used to release the shared global read access of a lock when
/// dropped.
///
/// This structure is created by the [`read`] and [`try_read`] methods on
/// [`SubfieldRwLock`].
///
/// [`SubfieldRwLock`]: super::lock::SubfieldRwLock
/// [`read`]: super::lock::SubfieldRwLock::read
/// [`try_read`]: super::lock::SubfieldRwLock::try_read
#[must_use = "if unused the SubfieldRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct SubfieldRwLockReadGuard<'a, T: ?Sized + 'a> {
    pub(super) metadata: &'a Metadata,
    pub(super) data: &'a T,
    // For opting-out of `Send`.
    pub(super) phantom: PhantomData<*const ()>,
}

impl<T: ?Sized> Deref for SubfieldRwLockReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.data
    }
}

impl<T: ?Sized> Drop for SubfieldRwLockReadGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        //         The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            self.metadata.lock.drop_subfield_reader_unchecked();
        }
    }
}

impl<T: ?Sized + Debug> Debug for SubfieldRwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized + Display> Display for SubfieldRwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: ?Sized + Sync> Sync for SubfieldRwLockReadGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::SubfieldRwLockReadGuard;
    use crate::core::Metadata;
    use std::{
        fmt::{self, Debug, Display},
        marker::PhantomData,
        mem,
        ops::{Deref, Drop},
    };

    /// RAII structure used to release the shared subfield read access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`SubfieldRwLockReadGuard`].
    ///
    /// [`map`]: super::SubfieldRwLockReadGuard::map
    /// [`filter_map`]: super::SubfieldRwLockReadGuard::filter_map
    #[must_use = "if unused the SubfieldRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedSubfieldRwLockReadGuard<'a, T: ?Sized + 'a> {
        metadata: &'a Metadata,
        data: &'a T,
        phantom: PhantomData<*const ()>, // For opting-out of `Send`.
    }

    impl<'a, T: ?Sized> SubfieldRwLockReadGuard<'a, T> {
        /// Makes a [`MappedSubfieldRwLockReadGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SubfieldRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SubfieldRwLockReadGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `SubfieldRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedSubfieldRwLockReadGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            let metadata = orig.metadata;
            let data = f(orig.data);
            mem::forget(orig);
            MappedSubfieldRwLockReadGuard {
                metadata,
                data,
                phantom: PhantomData,
            }
        }

        /// Makes a [`MappedSubfieldRwLockReadGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SubfieldRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SubfieldRwLockReadGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `SubfieldRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedSubfieldRwLockReadGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            let data = f(orig.data);
            match data {
                Some(data) => {
                    let metadata = orig.metadata;
                    mem::forget(orig);
                    Ok(MappedSubfieldRwLockReadGuard {
                        metadata,
                        data,
                        phantom: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> MappedSubfieldRwLockReadGuard<'a, T> {
        /// Makes a [`MappedSubfieldRwLockReadGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SubfieldRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSubfieldRwLockReadGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedSubfieldRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedSubfieldRwLockReadGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            let data = f(orig.data);
            let metadata = orig.metadata;
            mem::forget(orig);
            MappedSubfieldRwLockReadGuard {
                metadata,
                data,
                phantom: PhantomData,
            }
        }

        /// Makes a [`MappedSubfieldRwLockReadGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SubfieldRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSubfieldRwLockReadGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedSubfieldRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SubfieldRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedSubfieldRwLockReadGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            let data = f(orig.data);
            match data {
                Some(data) => {
                    let metadata = orig.metadata;
                    mem::forget(orig);
                    Ok(MappedSubfieldRwLockReadGuard {
                        metadata,
                        data,
                        phantom: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<T: ?Sized> Deref for MappedSubfieldRwLockReadGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            self.data
        }
    }

    impl<T: ?Sized> Drop for MappedSubfieldRwLockReadGuard<'_, T> {
        fn drop(&mut self) {
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            //         The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.metadata.lock.drop_subfield_reader_unchecked();
            }
        }
    }

    impl<T: Debug + ?Sized> Debug for MappedSubfieldRwLockReadGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<T: Display + ?Sized> Display for MappedSubfieldRwLockReadGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<T: Sync + ?Sized> Sync for MappedSubfieldRwLockReadGuard<'_, T> {}
}
