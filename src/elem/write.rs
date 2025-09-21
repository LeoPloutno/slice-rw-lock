use super::lock::InnerElemRwLock;
use crate::inner::alloc::Allocation;
use std::{
    fmt::{self, Debug, Display},
    marker::PhantomData,
    ops::{Deref, DerefMut, Drop},
    thread,
};

/// RAII structure used to release the exclusive element write access of a lock when
/// dropped.
///
/// This structure is created by the [`write`] and [`try_write`] methods on
/// [`ElemRwLock`].
///
/// [`ElemRwLock`]: super::lock::ElemRwLock
/// [`write`]: super::lock::ElemRwLock::write
/// [`try_write`]: super::lock::ElemRwLock::try_write
#[must_use = "if unused the ElemRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ElemRwLockWriteGuard<'a, T>(
    pub(super) &'a mut InnerElemRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for ElemRwLockWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        &*unsafe { Allocation::get_elem_mut_disjoint(self.0.allocation, self.0.idx) }
    }
}

impl<T> DerefMut for ElemRwLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        &mut *unsafe { Allocation::get_elem_mut_disjoint(self.0.allocation, self.0.idx) }
    }
}

impl<T> Drop for ElemRwLockWriteGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
        if thread::panicking() {
            metadata.state.poison();
        }
        unsafe {
            // SAFETY: The counter is guaranteed to be at least `1` because
            // when constructing `self` it has been incremented
            metadata.lock.drop_writer_unchecked();
        }
    }
}

impl<T: Debug> Debug for ElemRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: Display> Display for ElemRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for ElemRwLockWriteGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    use super::ElemRwLockWriteGuard;
    use crate::inner::{Metadata, alloc::Allocation};

    impl<'a, T> ElemRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedElemRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElemRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ElemRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        fn map<U, F>(orig: Self, f: F) -> MappedElemRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the element
            MappedElemRwLockWriteGuard {
                lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                data: NonNull::from_mut(f(unsafe {
                    Allocation::get_elem_mut_disjoint(orig.0.allocation, orig.0.idx)
                })),
            }
        }

        /// Makes a [`MappedElemRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElemRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ElemRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElemRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the element
            match f(unsafe { Allocation::get_elem_mut_disjoint(orig.0.allocation, orig.0.idx) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElemRwLockWriteGuard {
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_mut(data),
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
    /// on [`ElemRwLockWriteGuard`].
    ///
    /// [`map`]: super::ElemRwLockWriteGuard::map
    /// [`filter_map`]: super::ElemRwLockWriteGuard::filter_map
    #[must_use = "if unused the ElemRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedElemRwLockWriteGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T: ?Sized + 'a> MappedElemRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedElemRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElemRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedElemRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedElemRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let orig = ManuallyDrop::new(orig);
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            MappedElemRwLockWriteGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedElemRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElemRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedElemRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedElemRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            match f(unsafe { orig.data.as_mut() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElemRwLockWriteGuard {
                        lock: orig.lock,
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedElemRwLockWriteGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> DerefMut for MappedElemRwLockWriteGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_mut() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedElemRwLockWriteGuard<'a, T> {
        fn drop(&mut self) {
            // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
            if thread::panicking() {
                self.lock.state.poison();
            }
            unsafe {
                // SAFETY: The counter is guaranteed to be at least `1` because
                // when constructing `self` it has been incremented
                self.lock.lock.drop_writer_unchecked();
            }
        }
    }

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedElemRwLockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedElemRwLockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedElemRwLockWriteGuard<'a, T> {}
}
