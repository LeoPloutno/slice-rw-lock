use super::{
    iter::Iter, read_all::SliceRwLockReadAllGuard, write::SliceRwLockWriteGuard, write_all::SliceRwLockWriteAllGuard,
};
use crate::{
    array::lock::InnerArrayRwLock, inner::{alloc::Allocation, LockState}, slice::{chunks::Chunks, chunks_exact::ChunksExact, rchunks::RChunks, rchunks_exact::RChunksExact}, ArrayRwLock, ElemRwLock
};
use std::{
    alloc::{Allocator, Global}, fmt::{self, Debug, Formatter}, marker::PhantomData, mem::{self, ManuallyDrop, MaybeUninit}, num::NonZeroUsize, ops::OneSidedRange, option, panic::{RefUnwindSafe, UnwindSafe}, process, ptr::NonNull, sync::{
        atomic::{self, Ordering}, LockResult, PoisonError, TryLockError, TryLockResult
    }
};

pub(crate) struct InnerSliceRwLock<T> {
    pub(crate) start: usize,
    pub(crate) len: usize,
    pub(crate) allocation: NonNull<Allocation<T>>,
}

#[clippy::has_significant_drop]
pub struct SliceRwLock<T, A: Allocator = Global> {
    pub(crate) inner: InnerSliceRwLock<T>,
    pub(crate) allocator: A,
}

impl<T, A: Allocator> SliceRwLock<T, A> {
    /// Creates a new lock to the underlying `allocation`. Atomically increments the reference counter.
    ///
    /// # Safety
    /// `allocation` must point to a live and valid instance of `Allocation<T>`
    pub(crate) unsafe fn new(start: usize, len: usize, allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        if unsafe {
            Allocation::get_metadata_disjoint(allocation)
                .state
                .fetch_increment_counter_unchecked(Ordering::Release)
        } == LockState::MAX_COUNT
        {
            process::abort();
        }
        Self {
            allocator,
            inner: InnerSliceRwLock { start, len, allocation },
        }
    }

    /// Locks the allocation guarded by this 'SliceRwLock' with shared global read access, blocking
    /// the current thread until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more subfield nor global writers which
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
    /// This function will return an error if the `SliceRwLock` is poisoned. An
    /// `SliceRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired. The acquired lock guard will be contained in the returned
    /// error.
    pub fn read_all(&self) -> LockResult<SliceRwLockReadAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.read_all();
        let guard = SliceRwLockReadAllGuard(&self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to acquire this `SliceRwLock` with shared global read access.
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
    /// This function will return the [`Poisoned`] error if the `SliceRwLock` is
    /// poisoned. An `SliceRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `SliceRwLock` could
    /// not be acquired because it was already locked exclusively.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_read_all(&self) -> TryLockResult<SliceRwLockReadAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_read_all() {
            let guard = SliceRwLockReadAllGuard(&self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the element guarded by this `SliceRwLock` with exclusive subfiield write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while a global writer or any readers
    /// currently have access to the guarded allocation.
    /// It will, however, return if there are only other subfield writers currently.
    ///
    /// Returns an RAII guard which will release this thread's exclusive access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `SliceRwLock` is poisoned. An
    /// `SliceRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write(&mut self) -> LockResult<SliceRwLockWriteGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write();
        let guard = SliceRwLockWriteGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `SliceRwLock` with exclusive subfield write access.
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
    /// This function will return the [`Poisoned`] error if the `SliceRwLock` is
    /// poisoned. An `SliceRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `SliceRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write(&mut self) -> TryLockResult<SliceRwLockWriteGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write() {
            let guard = SliceRwLockWriteGuard(&mut self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the allocation guarded by this `SliceRwLock` with exclusive global write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other writers or other readers
    /// currently have access to the lock.
    ///
    /// Returns an RAII guard which will release this thread's exclusive access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `SliceRwLock` is poisoned. An
    /// `SliceRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write_all(&mut self) -> LockResult<SliceRwLockWriteAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write_all();
        let guard = SliceRwLockWriteAllGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `SliceRwLock` with exclusive global write access.
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
    /// This function will return the [`Poisoned`] error if the `SliceRwLock` is
    /// poisoned. An `SliceRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `SliceRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write_all(&mut self) -> TryLockResult<SliceRwLockWriteAllGuard<'_, T>> {
        // SAFETY: `self.inner.allocation` is not deallocated until the last lock is dropped
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write_all() {
            let guard = SliceRwLockWriteAllGuard(&mut self.inner, PhantomData);
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
    /// elements are overwritten by known-good values, then the lock can be marked as un-poisoned. Or
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

impl<T, A: Allocator + Clone> SliceRwLock<T, A> {
    /// Returns locks to the first and the rest of the slice guarded by `self`, or `Err` containing the original lock if it is empty.
    pub fn split_first(mut self) -> Result<(ElemRwLock<T, A>, Self), Self> {
        if self.inner.len > 0 {
            Ok((
                // SAFETY: `self.inner.allocation` points to a live and valid allocation by construction
                unsafe { ElemRwLock::new(self.inner.start, self.inner.allocation, self.allocator.clone()) },
                {
                    unsafe {
                        // SAFETY: `self.inner.start + self.inner.len` is guaranteed to point within or right outside the allocation, so an
                        // increment cannot result in overflow
                        self.inner.start = self.inner.start.unchecked_add(1);
                        // SAFETY: Checked above that `self.inner.len` is greater than zero
                        self.inner.len = self.inner.len.unchecked_sub(1);
                    }
                    self
                },
            ))
        } else {
            Err(self)
        }
    }

    /// Returns locks to the last and the rest of the slice guarded by `self`, or `Err` containing the original lock if it is empty.
    pub fn split_last(mut self) -> Result<(ElemRwLock<T, A>, Self), Self> {
        if self.inner.len > 0 {
            Ok((
                unsafe {
                    // SAFETY: `self.inner.allocation` points to a live and valid allocation by construction
                    ElemRwLock::new(
                        self.inner
                            .start
                            // SAFETY: `self.inner.start + self.inner.len` is guaranteed to point within or right outside the allocation
                            .unchecked_add(
                                // SAFETY: Checked above that `self.inner.len` is greater than zero
                                self.inner.len.unchecked_sub(1),
                            ),
                        self.inner.allocation,
                        self.allocator.clone(),
                    )
                },
                {
                    // SAFETY: Checked above that `self.inner.len` is greater than zero
                    unsafe {
                        self.inner.len = self.inner.len.unchecked_sub(1);
                    }
                    self
                },
            ))
        } else {
            Err(self)
        }
    }

    /// Returns an array lock to the first `N` items in the slice guarded by `self` and a lock to the remaining slice.
    ///
    /// If the slice is not at least `N` in length, this will return `Err` containing the original lock.
    pub fn split_first_chunk<const N: usize>(mut self) -> Result<(ArrayRwLock<T, N, A>, Self), Self> {
        if self.inner.len >= N {
            Ok((
                // SAFETY: `self.inner.allocation` points to a live and valid allocation by construction
                unsafe { ArrayRwLock::new(self.inner.start, self.inner.allocation, self.allocator.clone()) },
                {
                    unsafe {
                        // SAFETY: `self.inner.start + self.inner.len` is guaranteed to point within or right outside the allocation.
                        // Checked above that `self.inner.len` is greater than or equal to `N`
                        self.inner.start = self.inner.start.unchecked_add(N);
                        // SAFETY: Checked above that `self.inner.len` is greater than or equal to `N`
                        self.inner.len = self.inner.len.unchecked_sub(N);
                    }
                    self
                },
            ))
        } else {
            Err(self)
        }
    }

    /// Returns an array lock to the last `N` items in the slice guarded by `self` and a lock to the remaining slice.
    ///
    /// If the slice is not at least `N` in length, this will return `Err` containing the original lock.
    pub fn split_last_chunk<const N: usize>(mut self) -> Result<(ArrayRwLock<T, N, A>, Self), Self> {
        if self.inner.len >= N {
            Ok((
                // SAFETY: `self.inner.allocation` points to a live and valid allocation by construction
                unsafe {
                    ArrayRwLock::new(
                        self.inner
                            .start
                            // SAFETY: `self.inner.start + self.inner.len` is guaranteed to point within or right outside the allocation
                            .unchecked_add(
                                // SAFETY: Checked above that `self.inner.len` is greater than or equal to `N`
                                self.inner.len.unchecked_sub(N),
                            ),
                        self.inner.allocation,
                        self.allocator.clone(),
                    )
                },
                {
                    unsafe {
                        // SAFETY: Checked above that `self.inner.len` is greater than or equal to `N`
                        self.inner.len = self.inner.len.unchecked_sub(N);
                    }
                    self
                },
            ))
        } else {
            Err(self)
        }
    }

    pub fn iter(self) -> Iter<T, A> {
        let orig = ManuallyDrop::new(self);
        Iter { 
            start: orig.inner.start, 
            len: orig.inner.len, 
            allocation: orig.inner.allocation, 
            // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
            allocator: unsafe { (&orig.allocator as *const A).read() },
        }
    }

    pub fn chunks(self, chunk_size: usize) -> Chunks<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");
        let orig = ManuallyDrop::new(self);
        Chunks {
            // SAFETY: Checked above that `chunk_size` is non-zero
            chunk_size: unsafe { NonZeroUsize::new_unchecked(chunk_size) },
            start: orig.inner.start,
            remainder: orig.inner.len,
            allocation: orig.inner.allocation,
            // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
            allocator: unsafe { (&orig.allocator as *const A).read() },
        }
    }

    pub fn chunks_exact(self, chunk_size: usize) -> ChunksExact<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");
        // SAFETY: Checked above that `chunk_size` is non-zero
        let chunk_size = unsafe { NonZeroUsize::new_unchecked(chunk_size) };
        let remainder = self.inner.len % chunk_size;
        let orig = ManuallyDrop::new(self);
        ChunksExact {
            chunk_size,
            start: orig.inner.start,
            len: orig.inner.len / chunk_size,
            remainder: super::chunks_exact::Chunk {
                // SAFETY: `self.inner.start + self.inner.len` is guaranteed to point within or right outside the allocation.
                // `remainder` is less than `self.inner.len` by construction
                start: unsafe { orig.inner.start.unchecked_add(orig.inner.len).unchecked_sub(remainder) },
                len: remainder
            },
            allocation: orig.inner.allocation,
            // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
            allocator: unsafe { (&orig.allocator as *const A).read() },
        }
    }

    pub fn rchunks(self, chunk_size: usize) -> RChunks<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");
        let orig = ManuallyDrop::new(self);
        RChunks {
            // SAFETY: Checked above that `chunk_size` is non-zero
            chunk_size: unsafe { NonZeroUsize::new_unchecked(chunk_size) },
            // SAFETY: `self.inner.start + self.inner.len` is guaranteed to point within or right outside the allocation
            end: unsafe { orig.inner.start.unchecked_add(orig.inner.len) },
            remainder: orig.inner.len,
            allocation: orig.inner.allocation,
            // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
            allocator: unsafe { (&orig.allocator as *const A).read() },
        }
    }

    pub fn rchunks_exact(self, chunk_size: usize) -> RChunksExact<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");
        // SAFETY: Checked above that `chunk_size` is non-zero
        let chunk_size = unsafe { NonZeroUsize::new_unchecked(chunk_size) };
        let orig = ManuallyDrop::new(self);
        RChunksExact {
            chunk_size,
            // SAFETY: `self.inner.start + self.inner.len` is guaranteed to point within or right outside the allocation
            end: unsafe { orig.inner.start.unchecked_add(orig.inner.len) },
            len: orig.inner.len / chunk_size,
            remainder: super::rchunks_exact::Chunk {
                start: orig.inner.start,
                len: orig.inner.len % chunk_size
            },
            allocation: orig.inner.allocation,
            // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
            allocator: unsafe { (&orig.allocator as *const A).read() },
        }
    }

    pub fn chubk_by<F>(self, pred: F) -> ChunkBy<T, A, F>
    where 
        F: FnMut(&T, &T) -> bool
    {
        todo!()
    }

    pub fn split_at(self, mid: usize) -> (Self, Self) {
        todo!()
    }

    pub fn split_at_checked(self, mid: usize) -> Result<(Self, Self), Self> {
        todo!()
    }

    pub fn split<F>(self, pref: F) -> Split<T, A, F> 
    where 
        F: FnMut(&T) -> bool
    {
        todo!()
    }

    pub fn split_inclusive<F>(self, pred: F) -> SplitInclusive<T, A, F>
    where 
        F: FnMut(&T) -> bool
    {
        todo!()
    }

    pub fn rsplit<F>(self, pred: F) -> RSplit<T, A, F>
    where 
        F: FnMut(&T) -> bool
    {
        todo!()
    }

    pub fn splitn<F>(self, pred: F) -> SplitN<T, A, F>
    where 
        F: FnMut(&T) -> bool
    {
        todo!()
    }

    pub fn rsplitn<F>(self, pred: F) -> RSplitN<T, A, F>
    where 
        F: FnMut(&T) -> bool
    {
        todo!()
    }

    pub fn split_off_first(&mut self) -> Option<ElemRwLock<T, A>> {
        todo!()
    }

    pub fn split_off_last(&mut self) -> Option<ElemRwLock<T, A>> {
        todo!()
    }
}

#[cfg(feature = "slice_as_array")]
impl<T, A: Allocator> SliceRwLock<T, A> {
    /// Gets a lock to the underlying array.
    ///
    /// If `N` is not exactly equal to the length of the slice guarded by `self`, then this method returns
    /// `Err` containing the original lock.
    pub fn into_array_rw_lock<const N: usize>(self) -> Result<ArrayRwLock<T, N, A>, Self> {
        if self.inner.len == N {
            let orig = ManuallyDrop::new(self);
            Ok(ArrayRwLock {
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
                allocator: unsafe { (&orig.allocator as *const A).read() },
                inner: InnerArrayRwLock {
                    start: orig.inner.start,
                    allocation: orig.inner.allocation,
                },
            })
        } else {
            Err(self)
        }
    }
}

impl<T, A: Allocator> SliceRwLock<MaybeUninit<T>, A> {
    /// Converts to `SliceRwLock<T, A>`.
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
    pub const unsafe fn assume_init(self) -> SliceRwLock<T, A> {
        // SAFETY: All fields of `self` are forgotten immediately after
        // reading them out of the pointers
        let allocator = unsafe { (&raw const self.allocator).read() };
        let inner = unsafe { (&raw const self.inner).read() };
        mem::forget(self);

        let (ptr, len) = inner.allocation.to_raw_parts();
        SliceRwLock {
            allocator,
            inner: InnerSliceRwLock {
                start: inner.start,
                len: inner.len,
                allocation: NonNull::from_raw_parts(ptr, len),
            },
        }
    }
}

impl<T, A: Allocator> Drop for SliceRwLock<T, A> {
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

impl<T: Debug, A: Allocator> Debug for SliceRwLock<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("SliceRwLock");
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
        d.field("start", &self.inner.start);
        d.field("len", &self.inner.len);
        d.field("poisoned", &self.is_poisoned());
        d.finish_non_exhaustive()
    }
}

unsafe impl<T: Send + Sync, A: Allocator> Send for SliceRwLock<T, A> {}

impl<T, A: Allocator> RefUnwindSafe for SliceRwLock<T, A> {}

impl<T, A: Allocator> UnwindSafe for SliceRwLock<T, A> {}
