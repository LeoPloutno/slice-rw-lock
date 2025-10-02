use super::lock::InnerArrayRwLock;
use crate::inner::alloc::Allocation;
use std::{
    fmt::{self, Debug},
    marker::PhantomData,
    ops::{Deref, DerefMut, Drop},
    thread,
};

/// RAII structure used to release the exclusive chunk write access of a lock when
/// dropped.
///
/// This structure is created by the [`write`] and [`try_write`] methods on
/// [`ArrayRwLock`].
///
/// [`ArrayRwLock`]: super::lock::ArrayRwLock
/// [`write`]: super::lock::ArrayRwLock::write
/// [`try_write`]: super::lock::ArrayRwLock::try_write
#[must_use = "if unused the ArrayRwLock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ArrayRwLockWriteGuard<'a, T, const N: usize>(
    pub(super) &'a mut InnerArrayRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T, const N: usize> Deref for ArrayRwLockWriteGuard<'_, T, N> {
    type Target = [T; N];

    fn deref(&self) -> &Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        unsafe { Allocation::get_chunk_disjoint::<N>(self.0.allocation, self.0.start) }
    }
}

impl<T, const N: usize> DerefMut for ArrayRwLockWriteGuard<'_, T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: The allocation is valid and alive.
        // Aliasing rules are protected by synchronization
        unsafe { Allocation::get_chunk_mut_disjoint(self.0.allocation, self.0.start) }
    }
}

impl<T, const N: usize> Drop for ArrayRwLockWriteGuard<'_, T, N> {
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

impl<T: Debug, const N: usize> Debug for ArrayRwLockWriteGuard<'_, T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync, const N: usize> Sync for ArrayRwLockWriteGuard<'_, T, N> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    use super::ArrayRwLockWriteGuard;
    use crate::inner::{Metadata, alloc::Allocation};

    impl<'a, T, const N: usize> ArrayRwLockWriteGuard<'a, T, N> {
        /// Makes a [`MappedArrayRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ArrayRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ArrayRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ArrayRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ArrayRwLock will be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedArrayRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut [T; N]) -> &mut U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the allocation
            MappedArrayRwLockWriteGuard {
                lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                data: NonNull::from_mut(f(unsafe {
                    Allocation::get_chunk_mut_disjoint(orig.0.allocation, orig.0.start)
                })),
            }
        }

        /// Makes a [`MappedArrayRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ArrayRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ArrayRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ArrayRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ArrayRwLock will be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedArrayRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut [T; N]) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: The lifetime of the allocation pointed to by
            // `orig.0.allocation` exceeds `'a` by the virtue of the latter
            // not exceeding the lifetime of the lock which keeps it alive.
            // Aliasing rules are upheld thanks to synchronization
            // and `orig` not holding a (mutable) reference to the allocation
            match f(unsafe { Allocation::get_chunk_mut_disjoint(orig.0.allocation, orig.0.start) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedArrayRwLockWriteGuard {
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    /// RAII structure used to release the exclusive subfield write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`ArrayRwLockWriteGuard`].
    ///
    /// [`map`]: super::ArrayRwLockWriteGuard::map
    /// [`filter_map`]: super::ArrayRwLockWriteGuard::filter_map
    #[must_use = "if unused the ArrayRwLock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedArrayRwLockWriteGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T: ?Sized + 'a> MappedArrayRwLockWriteGuard<'a, T> {
        /// Makes a [`MappedArrayRwLockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ArrayRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedArrayRwLockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedArrayRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ArrayRwLock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedArrayRwLockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let orig = ManuallyDrop::new(orig);
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            MappedArrayRwLockWriteGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedArrayRwLockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ArrayRwLock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedArrayRwLockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedArrayRwLockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ArrayRwLock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedArrayRwLockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock
            match f(unsafe { orig.data.as_mut() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedArrayRwLockWriteGuard {
                        lock: orig.lock,
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedArrayRwLockWriteGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> DerefMut for MappedArrayRwLockWriteGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one
            unsafe { self.data.as_mut() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedArrayRwLockWriteGuard<'a, T> {
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

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedArrayRwLockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedArrayRwLockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedArrayRwLockWriteGuard<'a, T> {}
}
