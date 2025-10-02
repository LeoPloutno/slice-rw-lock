use super::lock::InnerSliceRwLock;
use crate::inner::alloc::Allocation;
use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    ops::{Deref, DerefMut, Drop},
    thread,
};

/// RAII structure used to release the exclusive element write access of a lock when
/// dropped.
///
/// This structure is created by the [`write`] and [`try_write`] methods on
/// [`SliceRwLock`].
///
/// [`SliceRwLock`]: super::lock::SliceRwLock
/// [`write`]: super::lock::SliceRwLock::write
/// [`try_write`]: super::lock::SliceRwLock::try_write
#[must_use = "if unused the SliceRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct SliceRwLockWriteGuard<'a, T>(
    pub(super) &'a mut InnerSliceRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for SliceRwLockWriteGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        unsafe { Allocation::get_subslice_disjoint(self.0.allocation, self.0.start, self.0.len) }
    }
}

impl<T> DerefMut for SliceRwLockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        unsafe { Allocation::get_subslice_mut_disjoint(self.0.allocation, self.0.start, self.0.len) }
    }
}

impl<T> Drop for SliceRwLockWriteGuard<'_, T> {
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

impl<T: Debug> Debug for SliceRwLockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for SliceRwLockWriteGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    use super::SliceRwLockWriteGuard;
    use crate::inner::{Metadata, alloc::Allocation};

    impl<'a, T> SliceRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedSliceRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SliceRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `SliceRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedSliceRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut [T]) -> &mut U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the element
            MappedSliceRwLockWriteGuard {
                lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                data: NonNull::from_mut(f(unsafe {
                    Allocation::get_subslice_mut_disjoint(orig.0.allocation, orig.0.start, orig.0.len)
                })),
            }
        }

        /// Makes a [`MappedSliceRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SliceRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `SliceRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedSliceRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut [T]) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the element
            match f(unsafe { Allocation::get_subslice_mut_disjoint(orig.0.allocation, orig.0.start, orig.0.len) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedSliceRwLockWriteGuard {
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
    /// on [`SliceRwLockWriteGuard`].
    ///
    /// [`map`]: super::SliceRwLockWriteGuard::map
    /// [`filter_map`]: super::SliceRwLockWriteGuard::filter_map
    #[must_use = "if unused the SliceRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedSliceRwLockWriteGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T: ?Sized + 'a> MappedSliceRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedSliceRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSliceRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedSliceRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedSliceRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let orig = ManuallyDrop::new(orig);
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            MappedSliceRwLockWriteGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedSliceRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSliceRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedSliceRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedSliceRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            match f(unsafe { orig.data.as_mut() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedSliceRwLockWriteGuard {
                        lock: orig.lock,
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedSliceRwLockWriteGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> DerefMut for MappedSliceRwLockWriteGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_mut() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedSliceRwLockWriteGuard<'a, T> {
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

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedSliceRwLockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedSliceRwLockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedSliceRwLockWriteGuard<'a, T> {}
}
