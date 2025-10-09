use super::lock::InnerElemRwLock;
use crate::inner::alloc::Allocation;
use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    ops::{Deref, DerefMut, Drop},
    thread,
};

/// RAII structure used to release the exclusive global write access of an 'ElemRwLock' when
/// dropped.
///
/// This structure is created by the [`write_all`] and [`try_write_all`] methods on
/// [`ElemRwLock`].
///
/// [`ElemRwLock`]: super::lock::ElemRwLock
/// [`write_all`]: super::lock::ElemRwLock::write
/// [`try_write_all`]: super::lock::ElemRwLock::try_write
#[must_use = "if unused the ElemRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ElemRwLockWriteAllGuard<'a, T>(
    pub(super) &'a mut InnerElemRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for ElemRwLockWriteAllGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        // Aliasing rules are protected by synchronization.
        unsafe { &*Allocation::get_slice_mut_disjoint(self.0.allocation) }
    }
}

impl<T> DerefMut for ElemRwLockWriteAllGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        // Aliasing rules are protected by synchronization.
        unsafe { Allocation::get_slice_mut_disjoint(self.0.allocation) }
    }
}

impl<T> Drop for ElemRwLockWriteAllGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: By construction `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
        if thread::panicking() {
            metadata.state.poison();
        }
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        // The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            metadata.lock.drop_all_writer_unchecked();
        }
    }
}

impl<T: Debug> Debug for ElemRwLockWriteAllGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for ElemRwLockWriteAllGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::ElemRwLockWriteAllGuard;
    use crate::inner::{Metadata, alloc::Allocation};
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    /// RAII structure used to release the exclusive global write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`ElemRwLockWriteAllGuard`].
    ///
    /// [`map`]: super::ElemRwLockWriteAllGuard::map
    /// [`filter_map`]: super::ElemRwLockWriteAllGuard::filter_map
    #[must_use = "if unused the ElemRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedElemRwLockWriteAllGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T> ElemRwLockWriteAllGuard<'a, T> {
        /// Makes a [`MappedElemRwLockWriteAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElemRwLockWriteAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ElemRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElemRwLockWriteAllGuard<'a, U>
        where
            F: FnOnce(&mut [T]) -> &mut U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: All invariants are upheld by construction.
            unsafe {
                MappedElemRwLockWriteAllGuard {
                    lock: Allocation::get_metadata_disjoint(orig.0.allocation),
                    data: NonNull::from_mut(f(Allocation::get_slice_mut_disjoint(orig.0.allocation))),
                }
            }
        }

        /// Makes a [`MappedElemRwLockWriteAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElemRwLockWriteAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ElemRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElemRwLockWriteAllGuard<'a, U>, Self>
        where
            F: FnOnce(&mut [T]) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: All invariants are upheld by construction.
            match f(unsafe { Allocation::get_slice_mut_disjoint(orig.0.allocation) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElemRwLockWriteAllGuard {
                        // SAFETY: By construction, `allocation` points to live and valid data.
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized + 'a> MappedElemRwLockWriteAllGuard<'a, T> {
        /// Makes a [`MappedElemRwLockWriteAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElemRwLockWriteAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedElemRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedElemRwLockWriteAllGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let orig = ManuallyDrop::new(orig);
            MappedElemRwLockWriteAllGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedElemRwLockWriteAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElemRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElemRwLockWriteAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedElemRwLockWriteAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElemRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedElemRwLockWriteAllGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            match f(unsafe { orig.data.as_mut() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElemRwLockWriteAllGuard {
                        lock: orig.lock,
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedElemRwLockWriteAllGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> DerefMut for MappedElemRwLockWriteAllGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_mut() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedElemRwLockWriteAllGuard<'a, T> {
        fn drop(&mut self) {
            if thread::panicking() {
                self.lock.state.poison();
            }
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            // The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.lock.lock.drop_all_writer_unchecked();
            }
        }
    }

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedElemRwLockWriteAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedElemRwLockWriteAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedElemRwLockWriteAllGuard<'a, T> {}
}

#[cfg(feature = "downgrade")]
impl<'a, T> ElemRwLockWriteAllGuard<'a, T> {
    /// Downgrades a global-write-locked `ElemRwLockWriteAllGuard` into a global-read-locked [`ElemRwLockReadAllGuard`].
    ///
    /// This method will atomically change the state of the lock from exclusive global mode into
    /// shared global mode. This means that it is impossible for a writing thread to get in between a
    /// thread calling `downgrade` and the same thread reading whatever it wrote while it had the
    /// lock in write mode.
    ///
    /// Note that since we have the `ElemRwLockWriteAllGuard`, we know that the lock is already
    /// locked for writing, so this method cannot fail.
    ///
    /// [`ElemRwLockReadAllGuard`]: super::read_all::ElemRwLockReadAllGuard
    pub fn downgrade(s: Self) -> super::read_all::ElemRwLockReadAllGuard<'a, T> {
        unsafe {
            // SAFETY: By construction, `allocation` points to live and valid data.
            Allocation::get_metadata_disjoint(s.0.allocation)
                .lock
                // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
                // The existance of `s` guarantees that the counter is at least 1.
                .downgrade_unchecked();
        }
        let lock = {
            let ptr = s.0 as *const _;
            std::mem::forget(s);
            // SAFETY: The only reference to the pointee has been forgoten above.
            unsafe { &*ptr }
        };
        super::read_all::ElemRwLockReadAllGuard(lock, PhantomData)
    }

    /// Downgrades a global-write-locked `ElemRwLockWriteAllGuard` into a subfield-write-locked [`ElemRwLockWriteGuard`].
    ///
    /// This method will atomically change the state of the lock from exclusive global mode into
    /// exclusive subfield mode. This means that it is impossible for a writing thread to get in between a
    /// thread calling `downgrade` and the same thread reading whatever it wrote while it had the
    /// lock in write mode.
    ///
    /// Note that since we have the `ElemRwLockWriteAllGuard`, we know that the lock is already
    /// locked for writing, so this method cannot fail.
    ///
    /// [`ElemRwlockWriteGuard`]: super::write::ElemRwLockWriteGuard
    pub fn downgrade_write(s: Self) -> super::write::ElemRwLockWriteGuard<'a, T> {
        unsafe {
            // SAFETY: By construction, `allocation` points to live and valid data.
            Allocation::get_metadata_disjoint(s.0.allocation)
                .lock
                // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
                // The existance of `s` guarantees that the counter is at least 1.
                .downgrade_write_unchecked();
        }
        let lock = {
            let ptr = s.0 as *mut _;
            std::mem::forget(s);
            // SAFETY: The only reference to the pointee has been forgotten above.
            unsafe { &mut *ptr }
        };
        super::write::ElemRwLockWriteGuard(lock, PhantomData)
    }
}
