use super::{read::SubfieldRwLockReadGuard, write::SubfieldRwLockWriteGuard};
use crate::core::{Allocation, State};
use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug, Formatter},
    marker::{PhantomData, Unsize},
    ops::CoerceUnsized,
    panic::{RefUnwindSafe, UnwindSafe},
    process,
    ptr::NonNull,
    sync::{LockResult, PoisonError, TryLockError, TryLockResult, atomic::Ordering},
};

/// A reader-writer lock guarding a subfield of an object of type `T`.
///
/// This lock provides shared and exclusive subfield accesses to the subfield of the guarded object.
#[clippy::has_significant_drop]
pub(super) struct SubfieldRwLock<T: ?Sized, U: ?Sized, A: Allocator = Global> {
    pub(super) data: NonNull<T>,
    pub(super) allocation: NonNull<Allocation<U>>,
    allocator: A,
}

impl<T: ?Sized, U: ?Sized, A: Allocator> SubfieldRwLock<T, U, A> {
    /// Creates a new lock guarding `allocation` without incrementing the reference counter.
    ///
    /// # Safety
    ///
    /// - `data` must point to a live and valid instance of `T`.
    /// - `allocation` must point to a live and valid instance of `Allocation<U>`.
    /// - The reference counter must not be zero when this function is called.
    #[inline]
    pub(crate) const unsafe fn new_not_incremented(data: NonNull<T>, allocation: NonNull<Allocation<U>>, allocator: A) -> Self {
        Self { data, allocation, allocator }
    }

    /// Creates a new lock guarding a subfield of `allocation`. Atomically increments the reference counter.
    ///
    /// # Safety
    ///
    /// - `data` must point to a live and valid instance of `T`.
    /// - `allocation` must point to a live and valid instance of `Allocation<T>`.
    pub(crate) unsafe fn new(data: NonNull<T>, allocation: NonNull<Allocation<U>>, allocator: A) -> Self {
        if unsafe {
            Allocation::get_metadata_disjoint(allocation)
                .state
                .fetch_increment_counter_unchecked(Ordering::Release)
        } == State::MAX_COUNT
        {
            process::abort();
        }
        // SAFETY: User-upheld invariants.
        unsafe { Self::new_not_incremented(data, allocation, allocator) }
    }

    /// Locks the object guarded by this 'SubfieldRwLock' with shared subfield read access, blocking
    /// the current thread until it can be acquired.
    ///
    /// The calling thread will be blocked until there is no gobal writer which
    /// holds the lock to the guarded object. There may be other subfield readers, subfield writers
    /// or global readers currently when this method returns.
    /// This method does not provide any guarantees with
    /// respect to the ordering of whether contentious readers or writers will
    /// acquire the lock first.
    ///
    /// Returns an RAII guard which will release this thread's shared subfield access
    /// once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `SubfieldRwLock` is poisoned. An
    /// `SubfieldRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired. The acquired lock guard will be contained in the returned
    /// error.
    pub fn read(&self) -> LockResult<SubfieldRwLockReadGuard<'_, T>> {
        // SAFETY: By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        metadata.lock.read_subfield();
        let guard = SubfieldRwLockReadGuard {
            metadata,
            // SAFETY: - By construction, `data` points to live and valid data.
            //         - Aliasing rules are upheld via synchronization, which
            //           was established above.
            data: unsafe { self.data.as_ref() },
            phantom: PhantomData,
        };
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to acquire this `SubfieldRwLock` with shared subfield read access.
    ///
    /// If the access could not be granted at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared global access
    /// when it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the [`Poisoned`] error if the `SubfieldRwLock` is
    /// poisoned. An `SubfieldRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `SubfieldRwLock` could
    /// not be acquired because it was already locked with exclusive global access.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_read(&self) -> TryLockResult<SubfieldRwLockReadGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        if metadata.lock.try_read_subfield() {
            let guard = SubfieldRwLockReadGuard {
                metadata,
                // SAFETY: - By construction, `data` points to live and valid data.
                //         - Aliasing rules are upheld via synchronization, which
                //           was established above.
                data: unsafe { self.data.as_ref() },
                phantom: PhantomData,
            };
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the element guarded by this `SubfieldRwLock` with exclusive subfield write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other global readers and/or writers have access to the lock.
    ///
    /// Returns an RAII guard which will release this thread's exclusive subfield access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `SubfieldRwLock` is poisoned. An
    /// `SubfieldRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write(&mut self) -> LockResult<SubfieldRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        metadata.lock.write_subfield();
        let guard = SubfieldRwLockWriteGuard {
            metadata,
            data: self.data,
            variance: PhantomData,
        };
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `SubfieldRwLock` with exclusive subfield write access.
    ///
    /// If the lock could not be acquired at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the lock when
    /// it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the [`Poisoned`] error if the `SubfieldRwLock` is
    /// poisoned. An `SubfieldRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `SubfieldRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write(&mut self) -> TryLockResult<SubfieldRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        if metadata.lock.try_write_subfield() {
            let guard = SubfieldRwLockWriteGuard {
                metadata,
                data: self.data,
                variance: PhantomData,
            };
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Determines whether the lock is poisoned.
    ///
    /// If another thread is active, the lock can still become poisoned at any
    /// time. You should not trust a `false` value for program correctness
    /// without additional synchronization.
    #[inline]
    pub fn is_poisoned(&self) -> bool {
        // By construction, `allocation` points to live and valid data.
        unsafe { Allocation::get_metadata_disjoint(self.allocation) }.state.is_poisoned()
    }

    /// Clear the poisoned state from a lock.
    ///
    /// If the lock is poisoned, it will remain poisoned until this function is called by any
    /// lock guarding the same object. This allows
    /// recovering from a poisoned state and marking that it has recovered. For example, if the
    /// elements are overwritten by known-good values, then the lock can be marked as un-poisoned. Or
    /// possibly, the elements could be inspected to determine if they are in a consistent state, and if
    /// so the poison is removed.
    #[inline]
    pub fn clear_poison(&self) {
        // By construction, `allocation` points to live and valid data.
        unsafe { Allocation::get_metadata_disjoint(self.allocation) }.state.clear_poison();
    }
}

impl<T: ?Sized, U: ?Sized, A: Allocator> Drop for SubfieldRwLock<T, U, A> {
    fn drop(&mut self) {
        // SAFETY: - By construction, `allocation` points to live and valid data.
        //         - By construction, every increment of the counter is paired with exactly one decrement.
        //           The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            Allocation::drop_in_unchecked(self.allocation, &self.allocator);
        }
    }
}

impl<T: Debug, A: Allocator> Debug for SubfieldRwLock<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("SubfieldRwLock");
        match self.try_read() {
            Ok(guard) => {
                d.field("data", &&*guard);
            }
            Err(TryLockError::Poisoned(err)) => {
                d.field("data", &&**err.get_ref());
            }
            Err(TryLockError::WouldBlock) => {
                d.field("data", &format_args!("<locked>"));
            }
        }
        d.field("poisoned", &self.is_poisoned());
        d.finish_non_exhaustive()
    }
}

unsafe impl<T: ?Sized + Send + Sync, A: Allocator> Send for SubfieldRwLock<T, A> {}

unsafe impl<T: ?Sized + Send + Sync, A: Allocator> Sync for SubfieldRwLock<T, A> {}

impl<T: ?Sized, A: Allocator> UnwindSafe for SubfieldRwLock<T, A> {}

impl<T: ?Sized, A: Allocator> RefUnwindSafe for SubfieldRwLock<T, A> {}

impl<T, U, A> CoerceUnsized<SubfieldRwLock<U, A>> for SubfieldRwLock<T, A>
where
    T: Unsize<U>,
    U: ?Sized,
    A: Allocator,
{
}
