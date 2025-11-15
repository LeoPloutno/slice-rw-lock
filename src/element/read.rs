use super::lock::InnerElementRwLock;
use crate::core::Allocation;
use std::{
    fmt::{self, Debug, Display},
    marker::PhantomData,
    ops::{Deref, Drop},
};

/// RAII structure used to release the shared subfield read access of a lock when
/// dropped.
///
/// This structure is created by the [`read`] and [`try_read`] methods on
/// [`ElementRwLock`].
///
/// [`ElementRwLock`]: super::lock::ElementRwLock
/// [`read`]: super::lock::ElementRwLock::read
/// [`try_read`]: super::lock::ElementRwLock::try_read
#[must_use = "if unused the ElementRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ElementRwLockReadGuard<'a, T> {
    pub(super) lock: &'a InnerElementRwLock<T>,
    // For opting-out of `Send`.
    pub(super) phantom: PhantomData<*const ()>,
}

impl<T> Deref for ElementRwLockReadGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        //         Aliasing rules are upheld via synchronization.
        unsafe { Allocation::get_element_disjoint(self.lock.allocation, self.lock.index) }
    }
}

impl<T> Drop for ElementRwLockReadGuard<'_, T> {
    fn drop(&mut self) {
        unsafe {
            // SAFETY: By construction, `allocation` points to live and valid data.
            Allocation::get_metadata_disjoint(self.lock.allocation)
                .lock
                // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
                //         The existance of `self` guarantees that the counter is at least 1.
                .drop_reader_unchecked();
        }
    }
}

impl<T: Debug> Debug for ElementRwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: Display> Display for ElementRwLockReadGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for ElementRwLockReadGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::ElementRwLockReadGuard;
    use crate::core::{Allocation, Metadata};
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
    /// on [`ElementRwLockReadGuard`].
    ///
    /// [`map`]: super::ElementRwLockReadGuard::map
    /// [`filter_map`]: super::ElementRwLockReadGuard::filter_map
    #[must_use = "if unused the ElementRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedElementRwLockReadGuard<'a, T: ?Sized + 'a> {
        metadata: &'a Metadata,
        data: &'a T,
        phantom: PhantomData<*const ()>, // For opting-out of `Send`.
    }

    impl<'a, T> ElementRwLockReadGuard<'a, T> {
        /// Makes a [`MappedElementRwLockReadGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwLockReadGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ElementRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElementRwLockReadGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.lock.allocation);
                // SAFETY: By construction `allocation` points to live and valid data.
                //         Aliasing rules are upheld via synchronization.
                let data = f(Allocation::get_element_disjoint(orig.lock.allocation, orig.lock.index));
                mem::forget(orig);
                MappedElementRwLockReadGuard {
                    metadata,
                    data,
                    phantom: PhantomData,
                }
            }
        }

        /// Makes a [`MappedElementRwLockReadGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwLockReadGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ElementRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElementRwLockReadGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            unsafe {
                // SAFETY: By construction `allocation` points to live and valid data.
                let metadata = Allocation::get_metadata_disjoint(orig.lock.allocation);
                // SAFETY: By construction `allocation` points to live and valid data.
                //         Aliasing rules are upheld via synchronization.
                let data = f(Allocation::get_element_disjoint(orig.lock.allocation, orig.lock.index));
                match data {
                    Some(data) => {
                        mem::forget(orig);
                        Ok(MappedElementRwLockReadGuard {
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

    impl<'a, T: ?Sized> MappedElementRwLockReadGuard<'a, T> {
        /// Makes a [`MappedElementRwLockReadGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwLockReadGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedElementRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElementRwLockReadGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            let data = f(orig.data);
            let metadata = orig.metadata;
            mem::forget(orig);
            MappedElementRwLockReadGuard {
                metadata,
                data,
                phantom: PhantomData,
            }
        }

        /// Makes a [`MappedElementRwLockReadGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwLock` is already locked for reading, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwLockReadGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedElementRwLockReadGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElementRwLockReadGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            let data = f(orig.data);
            match data {
                Some(data) => {
                    let metadata = orig.metadata;
                    mem::forget(orig);
                    Ok(MappedElementRwLockReadGuard {
                        metadata,
                        data,
                        phantom: PhantomData,
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<T: ?Sized> Deref for MappedElementRwLockReadGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            self.data
        }
    }

    impl<T: ?Sized> Drop for MappedElementRwLockReadGuard<'_, T> {
        fn drop(&mut self) {
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            //         The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.metadata.lock.drop_reader_unchecked();
            }
        }
    }

    impl<T: Debug + ?Sized> Debug for MappedElementRwLockReadGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<T: Display + ?Sized> Display for MappedElementRwLockReadGuard<'_, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<T: Sync + ?Sized> Sync for MappedElementRwLockReadGuard<'_, T> {}
}
