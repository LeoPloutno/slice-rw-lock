use super::lock::InnerElementRwLock;
use crate::inner::Allocation;
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
/// [`ElementRwlock`].
///
/// [`ElementRwlock`]: super::lock::ElementRwlock
/// [`write`]: super::lock::ElementRwlock::write
/// [`try_write`]: super::lock::ElementRwlock::try_write
#[must_use = "if unused the ElementRwlock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ElementRwlockWriteGuard<'a, T>(
    pub(super) &'a mut InnerElementRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for ElementRwlockWriteGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        // Aliasing rules are protected by synchronization.
        unsafe { Allocation::get_elem_disjoint(self.0.allocation, self.0.idx) }
    }
}

impl<T> DerefMut for ElementRwlockWriteGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        // Aliasing rules are protected by synchronization.
        unsafe { Allocation::get_elem_mut_disjoint(self.0.allocation, self.0.idx) }
    }
}

impl<T> Drop for ElementRwlockWriteGuard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: By construction `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
        if thread::panicking() {
            metadata.state.poison();
        }
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        // The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            metadata.lock.drop_writer_unchecked();
        }
    }
}

impl<T: Debug> Debug for ElementRwlockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: Display> Display for ElementRwlockWriteGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for ElementRwlockWriteGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::ElementRwlockWriteGuard;
    use crate::inner::{Allocation, Metadata};
    use std::{
        fmt::{self, Debug, Display},
        mem::ManuallyDrop,
        ops::{Deref, DerefMut, Drop},
        ptr::NonNull,
        thread,
    };

    /// RAII structure used to release the exclusive element write access of a lock when
    /// dropped, which can point to a subfield of the protected data.
    ///
    /// This structure is created by the [`map`] and [`filter_map`] methods
    /// on [`ElementRwlockWriteGuard`].
    ///
    /// [`map`]: super::ElementRwlockWriteGuard::map
    /// [`filter_map`]: super::ElementRwlockWriteGuard::filter_map
    #[must_use = "if unused the ElementRwlock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedElementRwlockWriteGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T> ElementRwlockWriteGuard<'a, T> {
        /// Makes a [`MappedElementRwlockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwlockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ElementRwlockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElementRwlockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: All invariants are upheld by construction.
            unsafe {
                MappedElementRwlockWriteGuard {
                    lock: Allocation::get_metadata_disjoint(orig.0.allocation),
                    data: NonNull::from_mut(f(Allocation::get_elem_mut_disjoint(orig.0.allocation, orig.0.idx))),
                }
            }
        }

        /// Makes a [`MappedElementRwlockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwlockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ElementRwlockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElementRwlockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: All invariants are upheld by construction.
            match f(unsafe { Allocation::get_elem_mut_disjoint(orig.0.allocation, orig.0.idx) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElementRwlockWriteGuard {
                        // SAFETY: By construction, `allocation` points to live and valid data.
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized + 'a> MappedElementRwlockWriteGuard<'a, T> {
        /// Makes a [`MappedElementRwlockWriteGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwlockWriteGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedElementRwlockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will be poisoned.
        pub fn map<U, F>(mut orig: Self, f: F) -> MappedElementRwlockWriteGuard<'a, U>
        where
            F: FnOnce(&mut T) -> &mut U,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            let data = NonNull::from_mut(f(unsafe { orig.data.as_mut() }));
            let orig = ManuallyDrop::new(orig);
            MappedElementRwlockWriteGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedElementRwlockWriteGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwlockWriteGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedElementRwlockWriteGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will be poisoned.
        pub fn filter_map<U, F>(mut orig: Self, f: F) -> Result<MappedElementRwlockWriteGuard<'a, U>, Self>
        where
            F: FnOnce(&mut T) -> Option<&mut U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            match f(unsafe { orig.data.as_mut() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElementRwlockWriteGuard {
                        lock: orig.lock,
                        data: NonNull::from_mut(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedElementRwlockWriteGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> DerefMut for MappedElementRwlockWriteGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_mut() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedElementRwlockWriteGuard<'a, T> {
        fn drop(&mut self) {
            if thread::panicking() {
                self.lock.state.poison();
            }
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            // The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.lock.lock.drop_writer_unchecked();
            }
        }
    }

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedElementRwlockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedElementRwlockWriteGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedElementRwlockWriteGuard<'a, T> {}
}
