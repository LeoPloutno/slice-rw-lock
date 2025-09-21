use super::lock::InnerElemRwLock;
use crate::inner::alloc::Allocation;
use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    ops::{Deref, Drop},
};

/// RAII structure used to release the shared global read access of a lock when
/// dropped.
///
/// This structure is created by the [`read_all`] and [`try_read_all`] methods on
/// [`ElemRwLock`].
///
/// [`ElemRwLock`]: super::lock::ElemRwLock
/// [`read_all`]: super::lock::ElemRwLock::read_all
/// [`try_read_all`]: super::lock::ElemRwLock::try_read_all
#[must_use = "if unused the ElemRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ElemRwLockReadAllGuard<'a, T>(
    pub(super) &'a InnerElemRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for ElemRwLockReadAllGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        unsafe { Allocation::get_all_disjoint(self.0.allocation) }
    }
}

impl<T> Drop for ElemRwLockReadAllGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
        unsafe {
            // SAFETY: The counter is guaranteed to be at least `1` because
            // when constructing `self` it has been incremented
            metadata.lock.drop_all_reader_unchecked();
        }
    }
}

impl<T: Debug> Debug for ElemRwLockReadAllGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for ElemRwLockReadAllGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, Drop},
        ptr::NonNull,
    };

    use super::ElemRwLockReadAllGuard;
    use crate::inner::{Metadata, alloc::Allocation};

    impl<'a, T> ElemRwLockReadAllGuard<'a, T> {
        /// Makes a [`MappedElemRwLockReadAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElemRwLockReadAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ElemRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will not be poisoned.
        fn map<U, F>(orig: Self, f: F) -> MappedElemRwLockReadAllGuard<'a, U>
        where
            F: FnOnce(&[T]) -> &U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the element
            MappedElemRwLockReadAllGuard {
                lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                data: NonNull::from_ref(f(unsafe { Allocation::get_all_disjoint(orig.0.allocation) })),
            }
        }

        /// Makes a [`MappedElemRwLockReadAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElemRwLockReadAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ElemRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will not be poisoned.
        fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElemRwLockReadAllGuard<'a, U>, Self>
        where
            F: FnOnce(&[T]) -> Option<&U>,
            U: ?Sized,
        {
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the element
            match f(unsafe { Allocation::get_all_disjoint(orig.0.allocation) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElemRwLockReadAllGuard {
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_ref(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    /// RAII structure used to release the exclusive element write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`ElemRwLockReadAllGuard`].
    ///
    /// [`map`]: super::ElemRwLockReadAllGuard::map
    /// [`filter_map`]: super::ElemRwLockReadAllGuard::filter_map
    #[must_use = "if unused the ElemRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedElemRwLockReadAllGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T: ?Sized + 'a> MappedElemRwLockReadAllGuard<'a, T> {
        /// Makes a [`MappedElemRwLockReadAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElemRwLockReadAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedElemRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElemRwLockReadAllGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            let data = NonNull::from_ref(f(unsafe { orig.data.as_ref() }));
            let orig = ManuallyDrop::new(orig);
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            MappedElemRwLockReadAllGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedElemRwLockReadAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElemRwLockReadAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedElemRwLockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElemRwLockReadAllGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            match f(unsafe { orig.data.as_ref() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElemRwLockReadAllGuard {
                        lock: orig.lock,
                        data: NonNull::from_ref(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedElemRwLockReadAllGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedElemRwLockReadAllGuard<'a, T> {
        fn drop(&mut self) {
            // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
            unsafe {
                // SAFETY: The counter is guaranteed to be at least `1` because
                // when constructing `self` it has been incremented
                self.lock.lock.drop_all_reader_unchecked();
            }
        }
    }

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedElemRwLockReadAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedElemRwLockReadAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedElemRwLockReadAllGuard<'a, T> {}
}
