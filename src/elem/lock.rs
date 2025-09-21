use super::{read_all::ElemRwLockReadAllGuard, write::ElemRwLockWriteGuard, write_all::ElemRwLockWriteAllGuard};
use crate::inner::alloc::Allocation;
use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
    mem::{self, MaybeUninit},
    panic::{RefUnwindSafe, UnwindSafe},
    ptr::NonNull,
    sync::{
        LockResult, PoisonError, TryLockError, TryLockResult,
        atomic::{self, Ordering},
    },
};

pub(crate) struct InnerElemRwLock<T> {
    pub(crate) idx: usize,
    pub(crate) allocation: NonNull<Allocation<T>>,
}

#[clippy::has_significant_drop]
pub struct ElemRwLock<T, A: Allocator = Global> {
    pub(crate) allocator: A,
    pub(crate) inner: InnerElemRwLock<T>,
}

impl<T, A: Allocator> ElemRwLock<T, A> {
    /// Locks the allocation guarded by this 'ElemRwLock' with shared global read access, blocking
    /// the current thread until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more element nor global writers which
    /// hold the locks to the guarded allocation. There may be other readers currently when
    /// this method returns. This method does not provide any guarantees with
    /// respect to the ordering of whether contentious readers or writers will
    /// acquire the lock first.
    ///
    /// Returns an RAII guard which will release this thread's shared access
    /// once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElemRwLock` is poisoned. An
    /// `ElemRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired. The acquired lock guard will be contained in the returned
    /// error.
    pub fn read_all(&self) -> LockResult<ElemRwLockReadAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.read_all();
        let guard = ElemRwLockReadAllGuard(&self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to acquire this `ElemRwLock` with shared global read access.
    ///
    /// If the access could not be granted at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared access
    /// when it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the [`Poisoned`] error if the `ElemRwLock` is
    /// poisoned. An `ElemRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ElemRwLock` could
    /// not be acquired because it was already locked exclusively.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_read_all(&self) -> TryLockResult<ElemRwLockReadAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_read_all() {
            let guard = ElemRwLockReadAllGuard(&self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the element guarded by this `ElemRwLock` with exclusive write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while a global writer or any readers
    /// currently have access to the guarded allocation.
    /// It will, however, return if there are only other element writers currently.
    ///
    /// Returns an RAII guard which will release this thread's exclusive access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElemRwLock` is poisoned. An
    /// `ElemRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write(&mut self) -> LockResult<ElemRwLockWriteGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write();
        let guard = ElemRwLockWriteGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `ElemRwLock` with exclusive element write access.
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
    /// This function will return the [`Poisoned`] error if the `RwLock` is
    /// poisoned. An `RwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `RwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write(&mut self) -> TryLockResult<ElemRwLockWriteGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write() {
            let guard = ElemRwLockWriteGuard(&mut self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the allocation guarded by this `ElemRwLock` with exclusive global write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other writers or other readers
    /// currently have access to the lock.
    ///
    /// Returns an RAII guard which will release this thread's exclusive access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElemRwLock` is poisoned. An
    /// `ElemRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write_all(&mut self) -> LockResult<ElemRwLockWriteAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write_all();
        let guard = ElemRwLockWriteAllGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `ElemRwLock` with exclusive global write access.
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
    /// This function will return the [`Poisoned`] error if the `RwLock` is
    /// poisoned. An `RwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `RwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write_all(&mut self) -> TryLockResult<ElemRwLockWriteAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write_all() {
            let guard = ElemRwLockWriteAllGuard(&mut self.inner, PhantomData);
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
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }
            .state
            .is_poisoned()
    }

    /// Clear the poisoned state from the allocation guarded by this lock.
    ///
    /// If the lock is poisoned, it will remain poisoned until this function is called by any lock guarding the same allocation. This allows
    /// recovering from a poisoned state and marking that it has recovered. For example, if the
    /// elements aree overwritten by known-good values, then the lock can be marked as un-poisoned. Or
    /// possibly, the elements could be inspected to determine if they are in a consistent state, and if
    /// so the poison is removed.
    #[inline]
    pub fn clear_poison(&self) {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }
            .state
            .clear_poison();
    }
}

impl<T, A: Allocator> ElemRwLock<MaybeUninit<T>, A> {
    /// Converts to `ElemRwLock<T, A>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the inner value
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    pub const unsafe fn assume_init(self) -> ElemRwLock<T, A> {
        // SAFETY: All fields of `self` are forgotten immediately after
        // reading them out of the pointers
        let allocator = unsafe { (&raw const self.allocator).read() };
        let inner = unsafe { (&raw const self.inner).read() };
        mem::forget(self);

        let (ptr, len) = inner.allocation.to_raw_parts();
        ElemRwLock {
            allocator,
            inner: InnerElemRwLock {
                allocation: NonNull::from_raw_parts(ptr, len),
                idx: inner.idx,
            },
        }
    }
}

impl<T, A: Allocator> Drop for ElemRwLock<T, A> {
    fn drop(&mut self) {
        // SAFETY: The counter is guaranteed to be at least `1` because
        // when constructing `self` it has been incremented
        if unsafe {
            Allocation::get_metadata_disjoint(self.inner.allocation)
                .state
                .fetch_decrement_counter_unchecked(Ordering::Release)
        } == 1
        {
            atomic::compiler_fence(Ordering::Acquire);
            unsafe {
                Allocation::deallocate_in(self.inner.allocation, &self.allocator);
            }
        }
    }
}

unsafe impl<T: Send + Sync> Send for ElemRwLock<T> {}

impl<T: Debug> Debug for ElemRwLock<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("ElemRwLock");
        match self.try_read_all() {
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
        d.field("idx", &self.inner.idx);
        d.field("poisoned", &self.is_poisoned());
        d.finish_non_exhaustive()
    }
}

impl<T, A: Allocator> RefUnwindSafe for ElemRwLock<T, A> {}

impl<T, A: Allocator> UnwindSafe for ElemRwLock<T, A> {}
