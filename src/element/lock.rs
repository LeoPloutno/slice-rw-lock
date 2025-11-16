use super::{read::ElementRwLockReadGuard, write::ElementRwLockWriteGuard};
use crate::core::{Allocation, State};
use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
    mem::{self, MaybeUninit},
    panic::{RefUnwindSafe, UnwindSafe},
    process,
    ptr::NonNull,
    sync::{LockResult, PoisonError, TryLockError, TryLockResult, atomic::Ordering},
};

pub(super) struct InnerElementRwLock<T> {
    pub(super) index: usize,
    pub(super) allocation: NonNull<Allocation<[T]>>,
}

/// A reader-writer lock guarding an element of a slice.
///
/// This lock provides shared and exclusive subfield accesses to a single element of the underlying slice.
#[clippy::has_significant_drop]
pub struct ElementRwLock<T, A: Allocator = Global> {
    pub(super) inner: InnerElementRwLock<T>,
    allocator: A,
}

impl<T, A: Allocator> ElementRwLock<T, A> {
    /// Creates a new lock guarding `allocation` without incrementing the reference counter.
    ///
    /// # Safety
    ///
    /// - `allocation` must point to a live and valid instance of `Allocation<[T]>`.
    /// - `idx` must index an element inside the array pointed to by `allocation`.
    /// - The reference counter must not be zero when this function is called.
    #[inline]
    pub(crate) const unsafe fn new_not_incremented(index: usize, allocation: NonNull<Allocation<[T]>>, allocator: A) -> Self {
        Self {
            inner: InnerElementRwLock { index, allocation },
            allocator,
        }
    }

    /// Creates a new lock guarding `allocation`. Atomically increments the reference counter.
    ///
    /// # Safety
    ///
    /// - `allocation` must point to a live and valid instance of `Allocation<[T]>`.
    /// - `idx` must index an element inside the array pointed to by `allocation`.
    pub(crate) unsafe fn new(index: usize, allocation: NonNull<Allocation<[T]>>, allocator: A) -> Self {
        if unsafe {
            Allocation::get_metadata_disjoint(allocation)
                .state
                .fetch_increment_counter_unchecked(Ordering::Release)
        } == State::MAX_COUNT
        {
            process::abort();
        }
        // SAFETY: User-upheld invariants.
        unsafe { Self::new_not_incremented(index, allocation, allocator) }
    }

    /// Locks the element guarded by this 'ElementRwLock' with shared subfield read access, blocking
    /// the current thread until it can be acquired.
    ///
    /// The calling thread will be blocked until there is no global writer which
    /// holds the lock to the guarded slice. There may be other subfield readers, global readers,
    /// and subfield writers currently when this method returns.
    /// This method does not provide any guarantees with
    /// respect to the ordering of whether contentious readers or writers will
    /// acquire the lock first.
    ///
    /// Returns an RAII guard which will release this thread's shared subfield access
    /// once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElementRwLock` is poisoned. An
    /// `ElementRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired. The acquired lock guard will be contained in the returned
    /// error.
    pub fn read(&self) -> LockResult<ElementRwLockReadGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.read_subfield();
        let guard = ElementRwLockReadGuard {
            lock: &self.inner,
            phantom: PhantomData,
        };
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to acquire this `ElementRwLock` with shared subfield read access.
    ///
    /// If the access could not be granted at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared subfield access
    /// when it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the [`Poisoned`] error if the `ElementRwLock` is
    /// poisoned. An `ElementRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ElementRwLock` could
    /// not be acquired because it was already locked with exclusive global access.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_read(&self) -> TryLockResult<ElementRwLockReadGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_read_subfield() {
            let guard = ElementRwLockReadGuard {
                lock: &self.inner,
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

    /// Locks the element guarded by this `ElementRwLock` with exclusive subfiield write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while a global writer or any global readers
    /// currently have access to the lock.
    /// It will, however, return if there are only other subfield readers and/or writers currently.
    ///
    /// Returns an RAII guard which will release this thread's exclusive subfield access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElementRwLock` is poisoned. An
    /// `ElementRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write(&mut self) -> LockResult<ElementRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write_subfield();
        let guard = ElementRwLockWriteGuard {
            lock: &self.inner,
            variance: PhantomData,
            phantom: PhantomData,
        };
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `ElementRwLock` with exclusive subfield write access.
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
    /// This function will return the [`Poisoned`] error if the `ElementRwLock` is
    /// poisoned. An `ElementRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ElementRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write(&mut self) -> TryLockResult<ElementRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write_subfield() {
            let guard = ElementRwLockWriteGuard {
                lock: &self.inner,
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
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }.state.is_poisoned()
    }

    /// Clear the poisoned state from a lock.
    ///
    /// If the lock is poisoned, it will remain poisoned until this function is called by any
    /// lock guarding the same slice. This allows
    /// recovering from a poisoned state and marking that it has recovered. For example, if the
    /// elements are overwritten by known-good values, then the lock can be marked as un-poisoned. Or
    /// possibly, the elements could be inspected to determine if they are in a consistent state, and if
    /// so the poison is removed.
    #[inline]
    pub fn clear_poison(&self) {
        // By construction, `allocation` points to live and valid data.
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }.state.clear_poison();
    }
}

impl<T, A: Allocator> ElementRwLock<MaybeUninit<T>, A> {
    /// Converts to `ElementRwLock<T, A>` wrapped in `Ok` if this is the only guard
    /// to the slice. Otherwise returns `Err` containing the original lock.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the inner slice
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    pub unsafe fn assume_init(self) -> Result<ElementRwLock<T, A>, Self> {
        // SAFETY: By construction, `allocation` points to live and valid data.
        if unsafe { Allocation::is_exclusive(self.inner.allocation) } {
            // SAFETY: Checked above that `self` is the only lock guarding the slice.
            Ok(unsafe { self.assume_init_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Converts to `ElementRwLock<T, A>`, assuming this is the only lock guarding the slice.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the inner slice
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// Calling this while another entity guarding the slice exists
    /// might lead to undefined behaviour when all guards are dropped.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    pub const unsafe fn assume_init_unchecked(self) -> ElementRwLock<T, A> {
        // SAFETY: All fields of `self` are forgotten immediately after
        //         reading them out of the pointers.
        let allocator = unsafe { (&raw const self.allocator).read() };
        let inner = unsafe { (&raw const self.inner).read() };
        mem::forget(self);

        let (ptr, len) = inner.allocation.to_raw_parts();
        ElementRwLock {
            allocator,
            inner: InnerElementRwLock {
                index: inner.index,
                allocation: NonNull::from_raw_parts(ptr, len),
            },
        }
    }
}

impl<T, A: Allocator> Drop for ElementRwLock<T, A> {
    fn drop(&mut self) {
        // SAFETY: - By construction, `allocation` points to live and valid data.
        //         - By construction, every increment of the counter is paired with exactly one decrement.
        //           The existance of `self` guarantees that the counter is at least 1.
        unsafe {
            Allocation::drop_in_unchecked(self.inner.allocation, &self.allocator);
        }
    }
}

impl<T: Debug, A: Allocator> Debug for ElementRwLock<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("ElementRwLock");
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
        d.field("index", &self.inner.index);
        d.field("poisoned", &self.is_poisoned());
        d.finish_non_exhaustive()
    }
}

unsafe impl<T: Send + Sync, A: Allocator> Send for ElementRwLock<T, A> {}

unsafe impl<T: Send + Sync, A: Allocator> Sync for ElementRwLock<T, A> {}

impl<T, A: Allocator> UnwindSafe for ElementRwLock<T, A> {}

impl<T, A: Allocator> RefUnwindSafe for ElementRwLock<T, A> {}
