use super::{read::WholeRwLockReadGuard, write::WholeRwLockWriteGuard};
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

/// A reader-writer lock guarding an object of type `T`.
///
/// This lock provides shared and exclusive global accesses to the whole underlying object.
#[clippy::has_significant_drop]
pub(super) struct WholeRwLock<T: ?Sized, A: Allocator = Global> {
    pub(super) allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T: ?Sized, A: Allocator> WholeRwLock<T, A> {
    /// Creates a new lock guarding `allocation` without incrementing the reference counter.
    ///
    /// # Safety
    ///
    /// - `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// - `idx` must index an element inside the array pointed to by `allocation`.
    /// - The reference counter must not be zero when this function is called.
    #[inline]
    pub(crate) const unsafe fn new_not_incremented(allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        Self { allocation, allocator }
    }

    /// Creates a new lock guarding `allocation`. Atomically increments the reference counter.
    ///
    /// # Safety
    ///
    /// - `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// - `idx` must index an element inside the array pointed to by `allocation`.
    pub(crate) unsafe fn new(allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        if unsafe {
            Allocation::get_metadata_disjoint(allocation)
                .state
                .fetch_increment_counter_unchecked(Ordering::Release)
        } == State::MAX_COUNT
        {
            process::abort();
        }
        // SAFETY: User-upheld invariants.
        unsafe { Self::new_not_incremented(allocation, allocator) }
    }

    /// Locks the object guarded by this 'WholeRwLock' with shared global read access, blocking
    /// the current thread until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no writers which
    /// hold the lock to the guarded object. There may be other subfield and/or global readers
    /// currently when this method returns.
    /// This method does not provide any guarantees with
    /// respect to the ordering of whether contentious readers or writers will
    /// acquire the lock first.
    ///
    /// Returns an RAII guard which will release this thread's shared global access
    /// once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `WholeRwLock` is poisoned. An
    /// `WholeRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired. The acquired lock guard will be contained in the returned
    /// error.
    pub fn read(&self) -> LockResult<WholeRwLockReadGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        metadata.lock.read_all();
        let guard = WholeRwLockReadGuard {
            allocation: self.allocation,
            phantom: PhantomData,
            variance: PhantomData,
        };
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to acquire this `WholeRwLock` with shared global read access.
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
    /// This function will return the [`Poisoned`] error if the `WholeRwLock` is
    /// poisoned. An `WholeRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `WholeRwLock` could
    /// not be acquired because it was already locked with global exclusive access.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_read(&self) -> TryLockResult<WholeRwLockReadGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        if metadata.lock.try_read_all() {
            let guard = WholeRwLockReadGuard {
                allocation: self.allocation,
                variance: PhantomData,
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

    /// Locks the element guarded by this `WholeRwLock` with exclusive global write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other readers and/or writers have access to the lock.
    ///
    /// Returns an RAII guard which will release this thread's exclusive subfield access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `WholeRwLock` is poisoned. An
    /// `WholeRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write(&mut self) -> LockResult<WholeRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        metadata.lock.write_all();
        let guard = WholeRwLockWriteGuard {
            allocation: self.allocation,
            variance: PhantomData,
            phantom: PhantomData,
        };
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `WholeRwLock` with exclusive global write access.
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
    /// This function will return the [`Poisoned`] error if the `WholeRwLock` is
    /// poisoned. An `WholeRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `WholeRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write(&self) -> TryLockResult<WholeRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
        if metadata.lock.try_write_all() {
            let guard = WholeRwLockWriteGuard {
                allocation: self.allocation,
                variance: PhantomData,
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

impl<T: ?Sized, A: Allocator> Drop for WholeRwLock<T, A> {
    fn drop(&mut self) {
        // SAFETY: - By construction, `allocation` points to live and valid data.
        //         - By construction, every increment of the counter is paired with exactly one decrement.
        //           The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            Allocation::drop_in_unchecked(self.allocation, &self.allocator);
        }
    }
}

impl<T: Debug, A: Allocator> Debug for WholeRwLock<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("WholeRwLock");
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

unsafe impl<T: ?Sized + Send + Sync, A: Allocator> Send for WholeRwLock<T, A> {}

unsafe impl<T: ?Sized + Send + Sync, A: Allocator> Sync for WholeRwLock<T, A> {}

impl<T: ?Sized, A: Allocator> UnwindSafe for WholeRwLock<T, A> {}

impl<T: ?Sized, A: Allocator> RefUnwindSafe for WholeRwLock<T, A> {}

impl<T, U, A> CoerceUnsized<WholeRwLock<U, A>> for WholeRwLock<T, A>
where
    T: Unsize<U>,
    U: ?Sized,
    A: Allocator,
{
}
