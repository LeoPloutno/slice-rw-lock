use super::lock::InnerSliceRwLock;
use crate::inner::Allocation;
use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    ops::{Deref, Drop},
};

/// RAII structure used to release the shared global read access of a lock when
/// dropped.
///
/// This structure is created by the [`read_all`] and [`try_read_all`] methods on
/// [`SliceRwLock`].
///
/// [`SliceRwLock`]: super::lock::SliceRwLock
/// [`read_all`]: super::lock::SliceRwLock::read_all
/// [`try_read_all`]: super::lock::SliceRwLock::try_read_all
#[must_use = "if unused the SliceRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct SliceRwLockReadAllGuard<'a, T>(
    pub(super) &'a InnerSliceRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for SliceRwLockReadAllGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        // Aliasing rules are protected by synchronization.
        unsafe { Allocation::get_slice_disjoint(self.0.allocation) }
    }
}

impl<T> Drop for SliceRwLockReadAllGuard<'_, T> {
    fn drop(&mut self) {
        unsafe {
            // SAFETY: By construction, `allocation` points to live and valid data.
            Allocation::get_metadata_disjoint(self.0.allocation)
                .lock
                // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
                // The existance of `self` guarantees that the counter is at least 1.
                .drop_all_reader_unchecked();
        }
    }
}

impl<T: Debug> Debug for SliceRwLockReadAllGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for SliceRwLockReadAllGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::SliceRwLockReadAllGuard;
    use crate::inner::{Allocation, Metadata};
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, Drop},
        ptr::NonNull,
    };

    /// RAII structure used to release the shared global write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`SliceRwLockReadAllGuard`].
    ///
    /// [`map`]: super::SliceRwLockReadAllGuard::map
    /// [`filter_map`]: super::SliceRwLockReadAllGuard::filter_map
    #[must_use = "if unused the SliceRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedSliceRwLockReadAllGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T> SliceRwLockReadAllGuard<'a, T> {
        /// Makes a [`MappedSliceRwLockReadAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SliceRwLockReadAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `SliceRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedSliceRwLockReadAllGuard<'a, U>
        where
            F: FnOnce(&[T]) -> &U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: All invariants are upheld by construction.
            unsafe {
                MappedSliceRwLockReadAllGuard {
                    lock: Allocation::get_metadata_disjoint(orig.0.allocation),
                    data: NonNull::from_ref(f(Allocation::get_slice_disjoint(orig.0.allocation))),
                }
            }
        }

        /// Makes a [`MappedSliceRwLockReadAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SliceRwLockReadAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `SliceRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedSliceRwLockReadAllGuard<'a, U>, Self>
        where
            F: FnOnce(&[T]) -> Option<&U>,
            U: ?Sized,
        {
            // SAFETY: By construction, `allocation` points to live and valid data.
            match f(unsafe { Allocation::get_slice_disjoint(orig.0.allocation) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedSliceRwLockReadAllGuard {
                        // SAFETY: By construction, `allocation` points to live and valid data.
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_ref(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized + 'a> MappedSliceRwLockReadAllGuard<'a, T> {
        /// Makes a [`MappedSliceRwLockReadAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSliceRwLockReadAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedSliceRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedSliceRwLockReadAllGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            let data = NonNull::from_ref(f(unsafe { orig.data.as_ref() }));
            let orig = ManuallyDrop::new(orig);
            MappedSliceRwLockReadAllGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedSliceRwLockReadAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSliceRwLockReadAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedSliceRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedSliceRwLockReadAllGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            match f(unsafe { orig.data.as_ref() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedSliceRwLockReadAllGuard {
                        lock: orig.lock,
                        data: NonNull::from_ref(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedSliceRwLockReadAllGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedSliceRwLockReadAllGuard<'a, T> {
        fn drop(&mut self) {
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            // The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.lock.lock.drop_all_reader_unchecked();
            }
        }
    }

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedSliceRwLockReadAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedSliceRwLockReadAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedSliceRwLockReadAllGuard<'a, T> {}
}
