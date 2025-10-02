use super::lock::InnerSliceRwLock;
use crate::inner::alloc::Allocation;
use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    ops::{Deref, DerefMut, Drop},
    thread,
};

/// RAII structure used to release the exclusive global write access of an 'SliceRwLock' when
/// dropped.
///
/// This structure is created by the [`write_all`] and [`try_write_all`] methods on
/// [`SliceRwLock`].
///
/// [`SliceRwLock`]: super::lock::SliceRwLock
/// [`write_all`]: super::lock::SliceRwLock::write
/// [`try_write_all`]: super::lock::SliceRwLock::try_write
#[must_use = "if unused the SliceRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct SliceRwLockWriteAllGuard<'a, T>(
    pub(super) &'a mut InnerSliceRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for SliceRwLockWriteAllGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        unsafe { &*Allocation::get_all_mut_disjoint(self.0.allocation) }
    }
}

impl<T> DerefMut for SliceRwLockWriteAllGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        unsafe { Allocation::get_all_mut_disjoint(self.0.allocation) }
    }
}

impl<T> Drop for SliceRwLockWriteAllGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: `self.0.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
        if thread::panicking() {
            metadata.state.poison();
        }
        unsafe {
            // SAFETY: The counter is guaranteed to be at least `1` because
            // when constructing `self` it has been incremented
            metadata.lock.drop_all_writer_unchecked();
        }
    }
}

impl<T: Debug> Debug for SliceRwLockWriteAllGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for SliceRwLockWriteAllGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    use super::SliceRwLockWriteAllGuard;
    use crate::inner::{Metadata, alloc::Allocation};

    impl<'a, T> SliceRwLockWriteAllGuard<'a, T> {
        /// Makes a [`MappedSliceRwLockWriteAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SliceRwLockWriteAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `SliceRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedSliceRwLockWriteAllGuard<'a, U>
        where
            F: FnOnce(&mut [T]) -> &mut U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the slice
            MappedSliceRwLockWriteAllGuard {
                lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                data: NonNull::from_mut(f(unsafe { Allocation::get_all_mut_disjoint(orig.0.allocation) })),
            }
        }

        /// Makes a [`MappedSliceRwLockWriteAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `SliceRwLockWriteAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `SliceRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedSliceRwLockWriteAllGuard<'a, U>, Self>
        where
            F: FnOnce(&mut [T]) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the slice
            match f(unsafe { Allocation::get_all_mut_disjoint(orig.0.allocation) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedSliceRwLockWriteAllGuard {
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    /// RAII structure used to release the exclusive global write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`SliceRwLockWriteAllGuard`].
    ///
    /// [`map`]: super::SliceRwLockWriteAllGuard::map
    /// [`filter_map`]: super::SliceRwLockWriteAllGuard::filter_map
    #[must_use = "if unused the SliceRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedSliceRwLockWriteAllGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T: ?Sized + 'a> MappedSliceRwLockWriteAllGuard<'a, T> {
        /// Makes a [`MappedSliceRwLockWriteAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSliceRwLockWriteAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedSliceRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedSliceRwLockWriteAllGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let orig = ManuallyDrop::new(orig);
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            MappedSliceRwLockWriteAllGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedSliceRwLockWriteAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `SliceRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedSliceRwLockWriteAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedSliceRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the SliceRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedSliceRwLockWriteAllGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            match f(unsafe { orig.data.as_mut() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedSliceRwLockWriteAllGuard {
                        lock: orig.lock,
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedSliceRwLockWriteAllGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> DerefMut for MappedSliceRwLockWriteAllGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_mut() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedSliceRwLockWriteAllGuard<'a, T> {
        fn drop(&mut self) {
            // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
            if thread::panicking() {
                self.lock.state.poison();
            }
            unsafe {
                // SAFETY: The counter is guaranteed to be at least `1` because
                // when constructing `self` it has been incremented
                self.lock.lock.drop_all_writer_unchecked();
            }
        }
    }

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedSliceRwLockWriteAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedSliceRwLockWriteAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedSliceRwLockWriteAllGuard<'a, T> {}
}

#[cfg(feature = "downgrade")]
impl<'a, T> SliceRwLockWriteAllGuard<'a, T> {
    /// Downgrades a global-write-locked `SliceRwLockWriteAllGuard` into a global-read-locked [`SliceRwLockReadAllGuard`].
    ///
    /// This method will atomically change the state of the lock from exclusive global mode into
    /// shared global mode. This means that it is impossible for a writing thread to get in between a
    /// thread calling `downgrade` and the same thread reading whatever it wrote while it had the
    /// lock in write mode.
    ///
    /// Note that since we have the `SliceRwLockWriteAllGuard`, we know that the lock is already
    /// locked for writing, so this method cannot fail.
    ///
    /// [`SliceRwLockReadAllGuard`]: super::read_all::SliceRwLockReadAllGuard
    pub fn downgrade(s: Self) -> super::read_all::SliceRwLockReadAllGuard<'a, T> {
        // SAFETY: `s.0.allocation` is not deallocated until the last lock is dropped
        // SAFETY: The counter is guaranteed to be at least `1` because
        // when constructing `s` it has been incremented
        unsafe {
            Allocation::get_metadata_disjoint(s.0.allocation)
                .lock
                .downgrade_unchecked();
        }
        let lock = {
            let ptr = s.0 as *const _;
            std::mem::forget(s);
            // SAFETY: The only reference to the pointee has already been forgotten
            unsafe { &*ptr }
        };
        super::read_all::SliceRwLockReadAllGuard(lock, PhantomData)
    }

    /// Downgrades a global-write-locked `SliceRwLockWriteAllGuard` into a subfield-write-locked [`SliceRwLockWriteGuard`].
    ///
    /// This method will atomically change the state of the lock from exclusive global mode into
    /// exclusive subfield mode. This means that it is impossible for a writing thread to get in between a
    /// thread calling `downgrade` and the same thread reading whatever it wrote while it had the
    /// lock in write mode.
    ///
    /// Note that since we have the `SliceRwLockWriteAllGuard`, we know that the lock is already
    /// locked for writing, so this method cannot fail.
    ///
    /// [`SliceRwlockWriteGuard`]: super::write::SliceRwLockWriteGuard
    pub fn downgrade_write(s: Self) -> super::write::SliceRwLockWriteGuard<'a, T> {
        // SAFETY: `s.0.allocation` is not deallocated until the last lock is dropped
        // SAFETY: The counter is guaranteed to be at least `1` because
        // when constructing `s` it has been incremented
        unsafe {
            Allocation::get_metadata_disjoint(s.0.allocation)
                .lock
                .downgrade_write_unchecked();
        }
        let lock = {
            let ptr = s.0 as *mut _;
            std::mem::forget(s);
            // SAFETY: The only reference to the pointee has already been forgotten
            unsafe { &mut *ptr }
        };
        super::write::SliceRwLockWriteGuard(lock, PhantomData)
    }
}
