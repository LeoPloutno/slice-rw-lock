use super::lock::InnerElementRwLock;
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
/// [`ElementRwlock`].
///
/// [`ElementRwlock`]: super::lock::ElementRwlock
/// [`read_all`]: super::lock::ElementRwlock::read_all
/// [`try_read_all`]: super::lock::ElementRwlock::try_read_all
#[must_use = "if unused the ElementRwlock will immediately unlock"]
#[clippy::has_significant_drop]
pub struct ElementRwlockReadAllGuard<'a, T>(
    pub(super) &'a InnerElementRwLock<T>,
    /* For opting-out of `Send` */ pub(super) PhantomData<*const ()>,
);

impl<T> Deref for ElementRwlockReadAllGuard<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY: By construction `allocation` points to live and valid data.
        // Aliasing rules are protected by synchronization.
        unsafe { Allocation::get_slice_disjoint(self.0.allocation) }
    }
}

impl<T> Drop for ElementRwlockReadAllGuard<'_, T> {
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

impl<T: Debug> Debug for ElementRwlockReadAllGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: Sync> Sync for ElementRwlockReadAllGuard<'_, T> {}

#[cfg(feature = "mapped_guards")]
pub(crate) mod mapped {
    use super::ElementRwlockReadAllGuard;
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
    /// on [`ElementRwlockReadAllGuard`].
    ///
    /// [`map`]: super::ElementRwlockReadAllGuard::map
    /// [`filter_map`]: super::ElementRwlockReadAllGuard::filter_map
    #[must_use = "if unused the ElementRwlock will immediately unlock"]
    #[clippy::has_significant_drop]
    pub struct MappedElementRwlockReadAllGuard<'a, T: ?Sized + 'a> {
        lock: &'a Metadata,
        data: NonNull<T>,
    }

    impl<'a, T> ElementRwlockReadAllGuard<'a, T> {
        /// Makes a [`MappedElementRwlockReadAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwlockReadAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `ElementRwlockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElementRwlockReadAllGuard<'a, U>
        where
            F: FnOnce(&[T]) -> &U,
            U: ?Sized,
        {
            let orig = ManuallyDrop::new(orig);
            // SAFETY: All invariants are upheld by construction.
            unsafe {
                MappedElementRwlockReadAllGuard {
                    lock: Allocation::get_metadata_disjoint(orig.0.allocation),
                    data: NonNull::from_ref(f(Allocation::get_slice_disjoint(orig.0.allocation))),
                }
            }
        }

        /// Makes a [`MappedElementRwlockReadAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `ElementRwlockReadAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `ElementRwlockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElementRwlockReadAllGuard<'a, U>, Self>
        where
            F: FnOnce(&[T]) -> Option<&U>,
            U: ?Sized,
        {
            // SAFETY: All invariants are upheld by construction.
            match f(unsafe { Allocation::get_slice_disjoint(orig.0.allocation) }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElementRwlockReadAllGuard {
                        // SAFETY: By construction, `allocation` points to live and valid data.
                        lock: unsafe { Allocation::get_metadata_disjoint(orig.0.allocation) },
                        data: NonNull::from_ref(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized + 'a> MappedElementRwlockReadAllGuard<'a, T> {
        /// Makes a [`MappedElementRwlockReadAllGuard`] for a component of the borrowed data, e.g.
        /// an enum variant.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwlockReadAllGuard::map(...)`. A method would interfere with methods of
        /// the same name on the contents of the `MappedElementRwlockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will not be poisoned.
        pub fn map<U, F>(orig: Self, f: F) -> MappedElementRwlockReadAllGuard<'a, U>
        where
            F: FnOnce(&T) -> &U,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            let data = NonNull::from_ref(f(unsafe { orig.data.as_ref() }));
            let orig = ManuallyDrop::new(orig);
            MappedElementRwlockReadAllGuard { lock: orig.lock, data }
        }

        /// Makes a [`MappedElementRwlockReadAllGuard`] for a component of the borrowed data. The
        /// original guard is returned as an `Err(...)` if the closure returns
        /// `None`.
        ///
        /// The `ElementRwlock` is already locked for writing, so this cannot fail.
        ///
        /// This is an associated function that needs to be used as
        /// `MappedElementRwlockReadAllGuard::filter_map(...)`. A method would interfere with methods
        /// of the same name on the contents of the `MappedElementRwlockReadAllGuard` used through
        /// `Deref`.
        ///
        /// # Panics
        ///
        /// If the closure panics, the guard will be dropped (unlocked) and the ElementRwlock will not be poisoned.
        pub fn filter_map<U, F>(orig: Self, f: F) -> Result<MappedElementRwlockReadAllGuard<'a, U>, Self>
        where
            F: FnOnce(&T) -> Option<&U>,
            U: ?Sized,
        {
            // SAFETY: No other pointer to the object can access it due to the
            // synchronization provided by the lock.
            match f(unsafe { orig.data.as_ref() }) {
                Some(data) => {
                    let orig = ManuallyDrop::new(orig);
                    Ok(MappedElementRwlockReadAllGuard {
                        lock: orig.lock,
                        data: NonNull::from_ref(data),
                    })
                }
                None => Err(orig),
            }
        }
    }

    impl<'a, T: ?Sized> Deref for MappedElementRwlockReadAllGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            // SAFETY: The only way to obtain a pointer to this pointee is to transform the only
            // guard protecting it via `map` or `filter_map`, which transfers ownership one-to-one.
            unsafe { self.data.as_ref() }
        }
    }

    impl<'a, T: ?Sized + 'a> Drop for MappedElementRwlockReadAllGuard<'a, T> {
        fn drop(&mut self) {
            // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
            // The existance of `self` guarantees that the counter is at least 1.
            unsafe {
                self.lock.lock.drop_all_reader_unchecked();
            }
        }
    }

    impl<'a, T: Debug + ?Sized + 'a> Debug for MappedElementRwlockReadAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    impl<'a, T: Display + ?Sized + 'a> Display for MappedElementRwlockReadAllGuard<'a, T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            (**self).fmt(f)
        }
    }

    unsafe impl<'a, T: Sync + ?Sized + 'a> Sync for MappedElementRwlockReadAllGuard<'a, T> {}
}
