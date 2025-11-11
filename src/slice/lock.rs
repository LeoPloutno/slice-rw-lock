#![allow(unused_imports)]
use super::{
    array_chunks::ArrayChunks, chunk_by::ChunkBy, chunks::Chunks, chunks_exact::ChunksExact, iter::Iter,
    panic_guard::PanicWriteGuard, rarray_chunks::RArrayChunks, rchunks::RChunks, rchunks_exact::RChunksExact,
    read_all::SliceRwLockReadAllGuard, rsplit::RSplit, rsplitn::RSplitN, split::Split, split_inclusive::SplitInclusive,
    splitn::SplitN, write::SliceRwLockWriteGuard, write_all::SliceRwLockWriteAllGuard,
};
use crate::{
    array::lock::ArrayRwLock,
    element::lock::ElementRwLock,
    inner::{self, Allocation, InnerRwLock, State},
};
#[cfg(feature = "strip_trim_prefix_suffix")]
use core::slice::SlicePattern;
use std::{
    alloc::{AllocError, Allocator, Global, Layout},
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    num::NonZeroUsize,
    ops::{OneSidedRange, OneSidedRangeBound, Range},
    panic::{RefUnwindSafe, UnwindSafe},
    process,
    ptr::NonNull,
    sync::{LockResult, PoisonError, TryLockError, TryLockResult, atomic::Ordering},
};

pub(super) struct InnerSliceRwLock<T> {
    pub(super) start: usize,
    pub(super) len: usize,
    pub(super) allocation: NonNull<Allocation<T>>,
}

#[clippy::has_significant_drop]
pub struct SliceRwLock<T, A: Allocator = Global> {
    pub(super) inner: InnerSliceRwLock<T>,
    allocator: A,
}

impl<T, A: Allocator> SliceRwLock<T, A> {
    /// Creates a new lock to the underlying `allocation` without incrementing the reference counter.
    ///
    /// # Safety
    ///
    /// * `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// * `start` must index an element inside the array pointed to by `allocation`.
    /// * `start + len` must either index an element of said array or point one element past its end.
    /// * The reference counter must not be zero when this function is called.
    #[inline]
    pub(crate) const unsafe fn new_not_incremented(
        start: usize,
        len: usize,
        allocation: NonNull<Allocation<T>>,
        allocator: A,
    ) -> Self {
        Self {
            allocator,
            inner: InnerSliceRwLock { start, len, allocation },
        }
    }

    /// Creates a new lock to the underlying `allocation`. Atomically increments the reference counter.
    ///
    /// # Safety
    ///
    /// * `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// * `start` must index an element inside the array pointed to by `allocation`.
    /// * `start + len` must either index an element of said array or point one element past its end.
    pub(crate) unsafe fn new(start: usize, len: usize, allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        if unsafe {
            Allocation::get_metadata_disjoint(allocation)
                .state
                .fetch_increment_counter_unchecked(Ordering::Release)
        } == State::MAX_COUNT
        {
            process::abort();
        }
        // SAFETY: User-upheld invariants.
        unsafe { Self::new_not_incremented(start, len, allocation, allocator) }
    }

    /// Returns a lock to the entire slice wrapped in `Ok` if `self` is the only
    /// entity guarding the slice. Otherwise, returns `Err` containing the original lock.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// let lock: SliceRwLock = vec![0, 1, 2].into();
    ///
    /// let all = lock.into_all();
    /// assert!(all.is_ok());
    ///
    /// let lock = all.unwrap();
    /// let (first_lock, tail_lock) = lock.split_first().unwrap();
    /// let not_all = tail_lock.into_all();
    /// assert!(not_all.is_err());
    ///
    /// let lock = not_all.unwrap_err();
    /// drop(first_lock);
    /// assert!(lock.into_all().is_ok());
    /// ```
    pub fn into_all(mut self) -> Result<SliceRwLock<T, A>, Self> {
        if self.is_all() {
            self.inner.start = 0;
            // SAFETY: By construction, `allocation` points to live and valid data.
            self.inner.len = Allocation::len(self.inner.allocation);
            Ok(self)
        } else {
            Err(self)
        }
    }

    /// Gets a lock to the underlying array.
    ///
    /// If `N` is not exactly equal to the length of the slice guarded by `self`, then this method returns
    /// `Err` containing the original lock.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    ///
    /// let array = slice.into_array::<3>();
    /// assert!(array.is_ok());
    ///
    /// let slice = array.unwrap().into_slice();
    /// let not_array = slice.into_array::<2>();
    /// assert!(not_array.is_err());
    /// ```
    #[cfg(feature = "slice_as_array")]
    pub const fn into_array<const N: usize>(self) -> Result<ArrayRwLock<T, N, A>, Self> {
        self.into_array_internal()
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
        // By construction, `allocation` points to live and valid data.
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
        // By construction, `allocation` points to live and valid data.
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
        // By construction, `allocation` points to live and valid data.
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
        // By construction, `allocation` points to live and valid data.
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
        // By construction, `allocation` points to live and valid data.
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
        // By construction, `allocation` points to live and valid data.
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
        // By construction, `allocation` points to live and valid data.
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
        // By construction, `allocation` points to live and valid data.
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }
            .state
            .clear_poison();
    }

    /// Returns the number of elements in the subslice guarded by this lock.
    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len
    }

    /// Returns the number of elements in the whole slice guarded by this lock.
    #[inline]
    pub const fn len_all(&self) -> usize {
        Allocation::len(self.inner.allocation)
    }

    /// Returns whether this lock is the only objject guarding the underlying slice.
    #[inline]
    pub fn is_all(&self) -> bool {
        // SAFETY: By construction, `allocation` points to live and valid data.
        unsafe { Allocation::is_exclusive(self.inner.allocation) }
    }

    /// Returns the range of indices of the subslice guarded by this lock.
    #[inline]
    pub const fn subslice_range(&self) -> Range<usize> {
        Range {
            start: self.inner.start,
            // SAFETY: By construction, `start + len` points within or right outside the allocation.
            end: unsafe { self.inner.start.unchecked_add(self.inner.len) },
        }
    }

    /// Returns an iterator over the guarded slice.
    ///
    /// The iterator yields locks to all items from start to end.
    pub fn iter(self) -> Iter<T, A> {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            Iter::new_unchecked_not_increment(
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to arrays of `N` elements of the guarded slice at a time, starting at the
    /// beginning of the slice.
    ///
    /// The chunks are slices and do not overlap. If `N` does not divide the length of the
    /// slice, then the last up to `N-1` elements will be omitted and can be retrieved
    /// from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `N` elements, the compiler can often optimize the
    /// resulting code better than in the case of [`chunks`].
    ///
    /// See [`chunks`] for a variant of this iterator that also returns the remainder as a smaller
    /// chunk, and [`rarray_chunks`] for the same iterator but starting at the end of the slice.
    ///
    /// # Panics
    ///
    /// Panics if `N` is zero.
    ///
    /// [`chunks`]: SliceRwLock::chunks
    /// [`rarray_chunks`]: SliceRwLock::rarray_chunks
    pub fn array_chunks<const N: usize>(self) -> ArrayChunks<T, N, A> {
        assert!(N != 0, "array size must be non-zero");

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            ArrayChunks::new_unchecked_not_increment(
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to `chunk_size` elements of the guarded slice at a time, starting at the
    /// beginning of the slice.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the length of the
    /// slice, then the last chunk will not have length `chunk_size`.
    ///
    /// See [`chunks_exact`] for a variant of this iterator that returns chunks of always exactly
    /// `chunk_size` elements, and [`rchunks`] for the same iterator but starting at the end of the
    /// slice.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is zero.
    ///
    /// [`chunks_exact`]: SliceRwLock::chunks_exact
    /// [`rchunks`]: SliceRwLock::rchunks
    pub fn chunks(self, chunk_size: usize) -> Chunks<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            Chunks::new_unchecked_not_increment(
                // SAFETY: Checked above that `chunk_size` is non-zero.
                NonZeroUsize::new_unchecked(chunk_size),
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to `chunk_size` elements of the guarded slice at a time, starting at the
    /// beginning of the slice.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the length of the
    /// slice, then the last up to `chunk_size-1` elements will be omitted and can be retrieved
    /// from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often optimize the
    /// resulting code better than in the case of [`chunks`].
    ///
    /// See [`chunks`] for a variant of this iterator that also returns the remainder as a smaller
    /// chunk, and [`rchunks_exact`] for the same iterator but starting at the end of the slice.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is zero.
    ///
    /// [`chunks`]: SliceRwLock::chunks
    /// [`rchunks_exact`]: SliceRwLock::rchunks_exact
    pub fn chunks_exact(self, chunk_size: usize) -> ChunksExact<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            ChunksExact::new_unchecked_not_increment(
                // SAFETY: Checked above that `chunk_size` is non-zero.
                NonZeroUsize::new_unchecked(chunk_size),
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to arrays of `N` elements of the guarded slice at a time, starting at the
    /// end of the slice.
    ///
    /// The chunks are slices and do not overlap. If `N` does not divide the length of the
    /// slice, then the last up to `N-1` elements will be omitted and can be retrieved
    /// from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `N` elements, the compiler can often optimize the
    /// resulting code better than in the case of [`rchunks`].
    ///
    /// See [`rchunks`] for a variant of this iterator that also returns the remainder as a smaller
    /// chunk, and [`array_chunks`] for the same iterator but starting at the beginning of the
    /// slice.
    ///
    /// # Panics
    ///
    /// Panics if `N` is zero.
    ///
    /// [`chunks`]: SliceRwLock::chunks
    /// [`rchunks`]: SliceRwLock::rchunks
    /// [`array_chunks`]: SliceRwLock::array_chunks
    pub fn rarray_chunks<const N: usize>(self) -> RArrayChunks<T, N, A> {
        assert!(N != 0, "array size must be non-zero");

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            RArrayChunks::new_unchecked_not_increment(
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to `chunk_size` elements of the guarded slice at a time, starting at the end
    /// of the slice.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the length of the
    /// slice, then the last chunk will not have length `chunk_size`.
    ///
    /// See [`rchunks_exact`] for a variant of this iterator that returns chunks of always exactly
    /// `chunk_size` elements, and [`chunks`] for the same iterator but starting at the beginning
    /// of the slice.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is zero.
    ///
    /// [`rchunks_exact`]: SliceRwLock::rchunks_exact
    /// [`chunks`]: SliceRwLock::chunks
    pub fn rchunks(self, chunk_size: usize) -> RChunks<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            RChunks::new_unchecked_not_increment(
                // SAFETY: Checked above that `chunk_size` is non-zero.
                NonZeroUsize::new_unchecked(chunk_size),
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to `chunk_size` elements of the guarded slice at a time, starting at the
    /// end of the slice.
    ///
    /// The chunks are slices and do not overlap. If `chunk_size` does not divide the length of the
    /// slice, then the last up to `chunk_size-1` elements will be omitted and can be retrieved
    /// from the `remainder` function of the iterator.
    ///
    /// Due to each chunk having exactly `chunk_size` elements, the compiler can often optimize the
    /// resulting code better than in the case of [`rchunks`].
    ///
    /// See [`rchunks`] for a variant of this iterator that also returns the remainder as a smaller
    /// chunk, and [`chunks_exact`] for the same iterator but starting at the beginning of the
    /// slice.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is zero.
    ///
    /// [`chunks`]: SliceRwLock::chunks
    /// [`rchunks`]: SliceRwLock::rchunks
    /// [`chunks_exact`]: SliceRwLock::chunks_exact
    pub fn rchunks_exact(self, chunk_size: usize) -> RChunksExact<T, A> {
        assert!(chunk_size != 0, "chunk size must be non-zero");

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            RChunksExact::new_unchecked_not_increment(
                // SAFETY: Checked above that `chunk_size` is non-zero.
                NonZeroUsize::new_unchecked(chunk_size),
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over the guarded slice producing non-overlapping runs
    /// of elements using the predicate to separate them.
    ///
    /// The unyielded elements are locked with exclusive access and the predicate is called for every pair of consecutive elements,
    /// meaning that it is called on `slice[0]` and `slice[1]`,
    /// followed by `slice[1]` and `slice[2]`, and so on.
    /// Once the oredicate returns `false`, the remaining elements are unlocked until the next iteration.
    ///
    /// # Panics
    ///
    /// If the predicate panics during evaluation, the panic is propagated.
    pub fn chunk_by<F>(self, pred: F) -> ChunkBy<T, F, A>
    where
        F: FnMut(&T, &T) -> bool,
    {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            ChunkBy::new_unchecked_not_increment(
                pred,
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to subslices separated by elements that match
    /// `pred`. The matched element is not contained in the subslices.
    ///
    /// At each iteration, The unyielded elements are locked with exclusive access until the separator is found.
    pub fn split<F>(self, pred: F) -> Split<T, F, A>
    where
        F: FnMut(&T) -> bool,
    {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            Split::new_unchecked_not_increment(
                pred,
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to subslices separated by elements that match
    /// `pred`. The matched element is contained in the end of the previous
    /// subslice as a terminator.
    ///
    /// At each iteration, The unyielded elements are locked with exclusive access until the separator is found.
    pub fn split_inclusive<F>(self, pred: F) -> SplitInclusive<T, F, A>
    where
        F: FnMut(&T) -> bool,
    {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            SplitInclusive::new_unchecked_not_increment(
                pred,
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to subslices separated by elements that match
    /// `pred`, starting at the end of the slice and working backwards.
    /// The matched element is not contained in the subslices.
    ///
    /// At each iteration, The unyielded elements are locked with exclusive access until the separator is found.
    pub fn rsplit<F>(self, pred: F) -> RSplit<T, F, A>
    where
        F: FnMut(&T) -> bool,
    {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            RSplit::new_unchecked_not_increment(
                pred,
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to subslices separated by elements that match
    /// `pred`, limited to returning at most `n` items. The matched element is
    /// not contained in the subslices.
    ///
    /// The last element returned, if any, will guard the remainder of the
    /// slice.
    ///
    /// At each iteration except the last one, The unyielded elements are locked with exclusive access until the separator is found.
    pub fn splitn<F>(self, n: usize, pred: F) -> SplitN<T, F, A>
    where
        F: FnMut(&T) -> bool,
    {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            SplitN::new_unchecked_not_increment(
                n,
                pred,
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }

    /// Returns an iterator over locks to subslices separated by elements that match
    /// `pred` limited to returning at most `n` items. This starts at the end of
    /// the slice and works backwards. The matched element is not contained in
    /// the subslices.
    ///
    /// The last element returned, if any, will guard the remainder of the
    /// slice.
    ///
    /// At each iteration except the last one, The unyielded elements are locked with exclusive access until the separator is found.
    pub fn rsplitn<F>(self, n: usize, pred: F) -> RSplitN<T, F, A>
    where
        F: FnMut(&T) -> bool,
    {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            RSplitN::new_unchecked_not_increment(
                n,
                pred,
                orig.inner.start,
                orig.inner.len,
                orig.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read(),
            )
        }
    }
}

impl<T, A: Allocator + Clone> SliceRwLock<T, A> {
    /// Returns locks to the first and the rest of the slice guarded by `self`, or `Err` containing the original lock if it is empty.
    pub fn split_first(mut self) -> Result<(ElementRwLock<T, A>, Self), Self> {
        if self.inner.len > 0 {
            let start_old = self.inner.start;
            unsafe {
                // SAFETY: By construction, `start + len` points within or right outside the allocation.
                self.inner.start = self.inner.start.unchecked_add(1);
                // SAFETY: Checked above that `len > 0`.
                self.inner.len = self.inner.len.unchecked_sub(1);

                Ok((
                    // SAFETY: By construction, `allocation` points to live and valid data.
                    ElementRwLock::new(start_old, self.inner.allocation, self.allocator.clone()),
                    self,
                ))
            }
        } else {
            Err(self)
        }
    }

    /// Returns locks to the last and the rest of the slice guarded by `self`, or `Err` containing the original lock if it is empty.
    pub fn split_last(mut self) -> Result<(ElementRwLock<T, A>, Self), Self> {
        if self.inner.len > 0 {
            unsafe {
                // SAFETY: Checked above that `len > 0`.
                self.inner.len = self.inner.len.unchecked_sub(1);
                Ok((
                    // SAFETY: By construction, `allocation` points to a live and valid data.
                    ElementRwLock::new(
                        // SAFETY: By construction, `start + len` points within or right outside the allocation.
                        self.inner.start.unchecked_add(self.inner.len),
                        self.inner.allocation,
                        self.allocator.clone(),
                    ),
                    self,
                ))
            }
        } else {
            Err(self)
        }
    }

    /// Returns an array lock to the first `N` items in the slice guarded by `self` and a lock to the remaining slice.
    ///
    /// If the slice is not at least `N` in length, this will return `Err` containing the original lock.
    pub fn split_first_chunk<const N: usize>(mut self) -> Result<(ArrayRwLock<T, N, A>, Self), Self> {
        if self.inner.len >= N {
            let start_old = self.inner.start;
            unsafe {
                // SAFETY: By construction, `start + len` points within or right outside the allocation.
                // Checked above that `len >= N`.
                self.inner.start = self.inner.start.unchecked_add(N);
                // SAFETY: Checked above that `len >= N`.
                self.inner.len = self.inner.len.unchecked_sub(N);
                Ok((
                    // SAFETY: By construction, `allocation` points to a live and valid data.
                    ArrayRwLock::new(start_old, self.inner.allocation, self.allocator.clone()),
                    self,
                ))
            }
        } else {
            Err(self)
        }
    }

    /// Returns an array lock to the last `N` items in the slice guarded by `self` and a lock to the remaining slice.
    ///
    /// If the slice is not at least `N` in length, this will return `Err` containing the original lock.
    pub fn split_last_chunk<const N: usize>(mut self) -> Result<(ArrayRwLock<T, N, A>, Self), Self> {
        if self.inner.len >= N {
            unsafe {
                // SAFETY: Checked above that `len >= N`.
                self.inner.len = self.inner.len.unchecked_sub(N);
                Ok((
                    // SAFETY: By construction, `allocation` points to a live and valid data.
                    ArrayRwLock::new(
                        // SAFETY: By construction, `start + len` does not overflow.
                        self.inner.start.unchecked_add(self.inner.len),
                        self.inner.allocation,
                        self.allocator.clone(),
                    ),
                    self,
                ))
            }
        } else {
            Err(self)
        }
    }

    /// Divides one lock to a slice into two at an index.
    ///
    /// The first will guard all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will guard all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// # Panics
    ///
    /// Panics if `mid > len`.  For a non-panicking alternative see
    /// [`split_at_checked`].
    ///
    /// [`split_at_checked`]: SliceRwLock::split_at_checked
    pub fn split_at(self, mid: usize) -> (Self, Self) {
        match self.split_at_checked(mid) {
            Ok(pair) => pair,
            Err(_) => panic!("mid > len"),
        }
    }

    /// Divides one lock to a slice into two at an index, without doing bounds checking.
    ///
    /// The first will guard all indices from `[0, mid)` (excluding
    /// the index `mid` itself) and the second will guard all
    /// indices from `[mid, len)` (excluding the index `len` itself).
    ///
    /// For a safe alternative see [`split_at`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used. The caller has to ensure that
    /// `0 <= mid <= self.len()`.
    ///
    /// [`split_at`]: SliceRwLock::split_at
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn split_at_unchecked(mut self, mid: usize) -> (Self, Self) {
        let start_old = self.inner.start;
        unsafe {
            // SAFETY: User-upheld invariant.
            self.inner.start = self.inner.start.unchecked_add(mid);
            // SAFETY: User-upheld invariant.
            self.inner.len = self.inner.len.unchecked_sub(mid);
            (
                Self::new(start_old, mid, self.inner.allocation, self.allocator.clone()),
                self,
            )
        }
    }

    /// Divides one lock to a slice into two at an index, returning `Err` if the slice is too short.
    ///
    /// If `mid ≤ len` returns a pair of locks where the first will guard all
    /// indices from `[0, mid)` (excluding the index `mid` itself) and the
    /// second will guard all indices from `[mid, len)` (excluding the index
    /// `len` itself).
    ///
    /// Otherwise, if `mid > len`, returns `Err` containing the original lock.
    pub fn split_at_checked(self, mid: usize) -> Result<(Self, Self), Self> {
        if mid <= self.inner.len {
            // SAFETY: Checked above that `mid <= len`.
            Ok(unsafe { self.split_at_unchecked(mid) })
        } else {
            Err(self)
        }
    }

    /// Splits the lock on the first element that matches the specified
    /// predicate.
    ///
    /// If any matching elements are present in the guarded slice, returns locks to the prefix
    /// before the match and suffix after.
    /// If no elements match, returns `Err` containing the original lock.
    ///
    /// Locks `self` with exclusive access.
    #[cfg(feature = "split_once")]
    pub fn split_once<F>(mut self, mut pred: F) -> Result<(Self, Self), Self>
    where
        F: FnMut(&T) -> bool,
    {
        // SAFETY: By construction, `start + len` points within or right outside the allocation.
        let end = unsafe { self.inner.start.unchecked_add(self.inner.len) };
        let mut curr = self.inner.start;
        let guard = unsafe {
            // SAFETY: The guard is dropped after the loop.
            PanicWriteGuard::new(
                // By construction, `allocation` points to live and valid data.
                &Allocation::get_metadata_disjoint(self.inner.allocation).lock,
            )
        };
        loop {
            if inner::unlikely(curr == end) {
                drop(guard);
                return Err(self);
            }
            // SAFETY: By construction, `allocation` points to live and valid data
            // and the accessed (sub)slice is locked behind local exclusive access.
            if pred(unsafe { Allocation::get_elem_disjoint(self.inner.allocation, curr) }) {
                break;
            } else {
                // SAFETY: Checked above that `curr != end`, which implies `curr < end`.
                curr = unsafe { curr.unchecked_add(1) };
            }
        }
        drop(guard);
        let start = self.inner.start;
        unsafe {
            // SAFETY: By construtcion, `curr < end`.
            self.inner.start = curr.unchecked_add(1);
            // SAFETY: By construction, `curr < end`, wich implies `0 <= end - curr - 1`.
            self.inner.len = end.unchecked_sub(self.inner.start);
            Ok((
                // SAFETY: All invariants are upheld by construction.
                Self::new(
                    start,
                    // SAFETY: By construction, `start <= curr`.
                    curr.unchecked_sub(self.inner.start),
                    self.inner.allocation,
                    self.allocator.clone(),
                ),
                self,
            ))
        }
    }

    /// Splits the lock on the last element that matches the specified
    /// predicate.
    ///
    /// If any matching elements are present in the guarded slice, returns locks to the prefix
    /// before the match and suffix after.
    /// If no elements match, returns `Err` containing the original lock.
    ///
    /// Locks `self` with exclusive access.
    #[cfg(feature = "split_once")]
    pub fn rsplit_once<F>(mut self, mut pred: F) -> Result<(Self, Self), Self>
    where
        F: FnMut(&T) -> bool,
    {
        // SAFETY: By construction, `start + len` points within or right outside the allocation.
        let end = unsafe { self.inner.start.unchecked_add(self.inner.len) };
        let mut curr = end;
        let guard = unsafe {
            // SAFETY: The guard is dropped after the loop.
            PanicWriteGuard::new(
                // By construction, `allocation` points to live and valid data.
                &Allocation::get_metadata_disjoint(self.inner.allocation).lock,
            )
        };
        loop {
            // SAFETY: By construction, `allocation` points to live and valid data
            // and the accessed (sub)slice is locked behind local exclusive access.
            if pred(unsafe { Allocation::get_elem_disjoint(self.inner.allocation, curr) }) {
                break;
            } else if inner::unlikely(curr == self.inner.start) {
                drop(guard);
                return Err(self);
            } else {
                // SAFETY: Checked above that `curr != start`, which implies `curr > end`.
                curr = unsafe { curr.unchecked_sub(1) };
            }
        }
        drop(guard);
        let start = self.inner.start;
        unsafe {
            // SAFETY: By construtcion, `curr < end`.
            self.inner.start = curr.unchecked_add(1);
            // SAFETY: By construction, `curr < end`, wich implies `0 <= end - curr - 1`.
            self.inner.len = end.unchecked_sub(self.inner.start);
            Ok((
                // SAFETY: All invariants are upheld by construction.
                Self::new(
                    start,
                    // SAFETY: By construction, `start <= curr`.
                    curr.unchecked_sub(self.inner.start),
                    self.inner.allocation,
                    self.allocator.clone(),
                ),
                self,
            ))
        }
    }

    // Returns a lock to a subslice with the prefix removed.
    //
    // If the guarded slice starts with `prefix`, returns a lock to the subslice after the prefix, wrapped in `Ok`.
    // If `prefix` is empty, simply returns a the original lock. If `prefix` is equal to the
    // original slice, returns a lock to an empty slice.
    //
    // If the slice does not start with `prefix`, returns `Err` containing the original lock.
    //
    // Locks `self` with exlcusive access.
    #[cfg(feature = "strip_trim_prefix_suffix")]
    pub fn strip_prefix<P>(mut self, prefix: &P) -> Result<Self, Self>
    where
        P: SlicePattern<Item = T> + ?Sized,
        T: PartialEq,
    {
        // SAFETY: By construction, `allocation` points to live and valid data.
        let lock = unsafe { &Allocation::get_metadata_disjoint(self.inner.allocation).lock };
        lock.write();
        // SAFETY: By construction, `alocation` points to live and valid data.
        // Aliasing rules are upheld via synchronization.
        let data =
            unsafe { Allocation::get_subslice_disjoint(self.inner.allocation, self.inner.start, self.inner.len) };
        let prefix = prefix.as_slice();
        let n = prefix.len();
        let ret = if n <= self.inner.len {
            // SAFETY: Checked above that `n < len`.
            let (head, _) = unsafe { data.split_at_unchecked(n) };
            if head == prefix {
                unsafe {
                    // SAFETY: Checked above that `n <= len`, which implies `start + n <= start + len`.
                    self.inner.start = self.inner.start.unchecked_add(n);
                    // SAFETY: Checked above that `n <= len`.
                    self.inner.len = self.inner.len.unchecked_sub(n);
                }
                Ok(self)
            } else {
                Err(self)
            }
        } else {
            Err(self)
        };
        // SAFETY: Locked the slice with `write` access previously.
        unsafe {
            lock.drop_writer_unchecked();
        }
        ret
    }

    // Returns a lock to a subslice with the suffix removed.
    //
    // If the guarded slice ends with `suffix`, returns a lock to the subslice before the suffix, wrapped in `Ok`.
    // If `suffix` is empty, simply returns the original lock. If `suffix` is equal to the
    // original slice, returns a lock to an empty slice.
    //
    // If the slice does not start with `suffix`, returns `Err` containing the original lock.
    //
    // Locks `self` with exclusive access.
    #[cfg(feature = "strip_trim_prefix_suffix")]
    pub fn strip_suffix<P>(mut self, suffix: &P) -> Result<Self, Self>
    where
        P: SlicePattern<Item = T> + ?Sized,
        T: PartialEq,
    {
        // SAFETY: By construction, `allocation` points to live and valid data.
        let lock = unsafe { &Allocation::get_metadata_disjoint(self.inner.allocation).lock };
        lock.write();
        // SAFETY: By construction, `alocation` points to live and valid data.
        // Aliasing rules are upheld via synchronization.
        let data =
            unsafe { Allocation::get_subslice_disjoint(self.inner.allocation, self.inner.start, self.inner.len) };
        let suffix = suffix.as_slice();
        let n = suffix.len();
        let ret = if n <= self.inner.len {
            // SAFETY: Checked above that `n < len`.
            let (_, tail) = unsafe { data.split_at_unchecked(self.inner.len.unchecked_sub(n)) };
            if tail == suffix {
                // SAFETY: Checked above that `n <= len`.
                unsafe {
                    self.inner.len = self.inner.len.unchecked_sub(n);
                }
                Ok(self)
            } else {
                Err(self)
            }
        } else {
            Err(self)
        };
        // SAFETY: Locked the slice with `write` access previously.
        unsafe {
            lock.drop_writer_unchecked();
        }
        ret
    }

    // Returns a lock to a subslice with the optional prefix removed.
    //
    // If the guarded slice starts with `prefix`, returns a lock to the subslice after the prefix. If `prefix`
    // is empty or the slice does not start with `prefix`, simply returns the original lock.
    // If `prefix` is equal to the original slice, returns a lock to an empty slice.
    //
    // Locks `self` with exclusive access.
    #[cfg(feature = "strip_trim_prefix_suffix")]
    pub fn trim_prefix<P>(self, prefix: &P) -> Self
    where
        P: SlicePattern<Item = T> + ?Sized,
        T: PartialEq,
    {
        match self.strip_prefix(prefix) {
            Ok(lock) => lock,
            Err(lock) => lock,
        }
    }

    // Returns a lock to a subslice with the optional suffix removed.
    //
    // If the guarded slice ends with `suffix`, returns a lock to the subslice before the suffix. If `suffix`
    // is empty or the slice does not end with `suffix`, simply returns the original lock.
    // If `suffix` is equal to the original slice, returns a lock to an empty slice.
    //
    // Locks `self` with exclusive access.
    #[cfg(feature = "strip_trim_prefix_suffix")]
    pub fn trim_suffix<P>(self, suffix: &P) -> Self
    where
        P: SlicePattern<Item = T> + ?Sized,
        T: PartialEq,
    {
        match self.strip_suffix(suffix) {
            Ok(lock) => lock,
            Err(lock) => lock,
        }
    }

    // Removes the subslice corresponding to the given range
    // and returns a lock to it.
    //
    // Returns `None` and does not modify the the lock if the given
    // range is out of bounds.
    //
    // Note that this method only accepts one-sided ranges such as
    // `2..` or `..6`, but not `2..6`.
    pub fn split_off<R>(&mut self, range: R) -> Option<Self>
    where
        R: OneSidedRange<usize>,
    {
        match range.bound() {
            (OneSidedRangeBound::End, bound_end) if bound_end <= self.inner.len => {
                let start_old = self.inner.start;
                unsafe {
                    // SAFETY: Checked above that `bound_end <= len`, which implies `start + end <= start + len`.
                    self.inner.start = self.inner.start.unchecked_add(bound_end);
                    // SAFETY: Checked above that `bound_end <= len`.
                    self.inner.len = self.inner.len.unchecked_sub(bound_end);
                    // SAFETY: All invariants are upheld by construction.
                    Some(Self::new(
                        start_old,
                        bound_end,
                        self.inner.allocation,
                        self.allocator.clone(),
                    ))
                }
            }
            (OneSidedRangeBound::EndInclusive, bound_end) if bound_end < self.inner.len => {
                let start_old = self.inner.start;
                unsafe {
                    // SAFETY: Checked above that `bound_end < len`, which implies `start + bound_end + 1 <= start + len`.
                    self.inner.start = self.inner.start.unchecked_add(bound_end).unchecked_add(1);
                    // SAFETY: Checked above that `bound_end < len`.
                    self.inner.len = self.inner.len.unchecked_sub(bound_end).unchecked_sub(1);
                    // SAFETY: All invariants are upheld by construction.
                    Some(Self::new(
                        start_old,
                        // SAFETY: Checked aboce that `bound_end < len`.
                        bound_end.unchecked_add(1),
                        self.inner.allocation,
                        self.allocator.clone(),
                    ))
                }
            }
            (OneSidedRangeBound::StartInclusive, bound_start) if bound_start < self.inner.len => {
                self.inner.len = bound_start;
                unsafe {
                    Some(Self::new(
                        // SAFETY: Checked above that `bound_start < len`,
                        // which implies `start + bound_start < start + len`.
                        self.inner.start.unchecked_add(bound_start),
                        // SAFETY: Checked above that `bound_start < len`.
                        self.inner.len.unchecked_sub(bound_start),
                        self.inner.allocation,
                        self.allocator.clone(),
                    ))
                }
            }
            _ => None,
        }
    }

    // Removes the first element of the guarded slice and returns a lock
    // to it.
    //
    // Returns `None` if the slice is empty.
    pub fn split_off_first(&mut self) -> Option<ElementRwLock<T, A>> {
        if self.inner.len >= 1 {
            let first = self.inner.start;
            unsafe {
                // SAFETY: Checked above that `1 <= len`, which implies `start + 1 <= start + len`.
                self.inner.start = self.inner.start.unchecked_add(1);
                // SAFETY: Checked above that `1 <= len`.
                self.inner.len = self.inner.len.unchecked_sub(1);
                // SAFETY: All invariants are upheld by construction.
                Some(ElementRwLock::new(first, self.inner.allocation, self.allocator.clone()))
            }
        } else {
            None
        }
    }

    // Removes the last element of the guarded slice and returns a lock
    // to it.
    //
    // Returns `None` if the slice is empty.
    pub fn split_off_last(&mut self) -> Option<ElementRwLock<T, A>> {
        if self.inner.len >= 1 {
            unsafe {
                // Checked above that `1 <= len`.
                self.inner.len = self.inner.len.unchecked_sub(1);
                Some(
                    // SAFETY: All invariants are upheld by construction.
                    ElementRwLock::new(
                        // SAFETY: Checked above that `1 <= len`, which implies `start + len - 1 >= start`.
                        self.inner.start.unchecked_add(self.inner.len),
                        self.inner.allocation,
                        self.allocator.clone(),
                    ),
                )
            }
        } else {
            None
        }
    }
}

impl<T, A: Allocator> SliceRwLock<T, A> {
    #[inline]
    pub(crate) const fn into_array_internal<const N: usize>(self) -> Result<ArrayRwLock<T, N, A>, Self> {
        if self.inner.len == N {
            Ok(unsafe {
                // SAFETY: All invariants are upheld by construction.
                let ret = ArrayRwLock::new_not_incremented(
                    self.inner.start,
                    self.inner.allocation,
                    // SAFETY: The allocator is not accessed after this line and is forgotten below.
                    (&self.allocator as *const A).read(),
                );
                mem::forget(self);
                ret
            })
        } else {
            Err(self)
        }
    }
}

impl<T> SliceRwLock<MaybeUninit<T>> {
    /// Constructs a new `SliceRwLock` with uninitialized contents.
    pub fn new_uninit(len: usize) -> Self {
        // SAFETY: All invariants are upheld by construction.
        unsafe { Self::new(0, len, Allocation::allocate_uninit_in(len, &Global), Global) }
    }

    /// Constructs a new `SliceRwLock` with uninitialized contents,
    /// with the memory being filled with `0` bytes.
    pub fn new_zeroed(len: usize) -> Self {
        // SAFETY: All invariants are upheld by construction.
        unsafe { Self::new(0, len, Allocation::allocate_zeroed_in(len, &Global), Global) }
    }

    /// Constructs a new `SliceRwlock` with uninitialized contents,
    /// returning an error if the allocation fails.
    #[cfg(feature = "allocator_api")]
    pub fn try_new_uninit(len: usize) -> Result<Self, AllocError> {
        // SAFETY: All invariants are upheld by construction.
        Allocation::try_allocate_uninit_in(len, &Global).map(|ptr| unsafe { Self::new(0, len, ptr, Global) })
    }

    /// Constructs a new `SliceRwLock` with uninitialized contents,
    /// with the memory being filled with `0` bytes,
    /// returning an error if the allocation fails.
    #[cfg(feature = "allocator_api")]
    pub fn try_new_zeroed(len: usize) -> Result<Self, AllocError> {
        // SAFETY: All invariants are upheld by construction.
        Allocation::try_allocate_zeroed_in(len, &Global).map(|ptr| unsafe { Self::new(0, len, ptr, Global) })
    }
}

impl<T, A: Allocator> SliceRwLock<MaybeUninit<T>, A> {
    /// Constructs a new `SliceRwLock` with uninitialized contents in the provided allocator.
    #[cfg(feature = "allocator_api")]
    pub fn new_uninit_in(len: usize, allocator: A) -> Self {
        // SAFETY: All invariants are upheld by construction.
        unsafe { Self::new(0, len, Allocation::allocate_uninit_in(len, &allocator), allocator) }
    }

    /// Constructs a new `SliceRwLock` with uninitialized contents,
    /// with the memory being filled with `0` bytes, in the provided allocator.
    ///
    /// See [`MaybeUninit::zeroed`] for examples of correct and incorrect
    /// usage of this method.
    ///
    /// [`Maybeuninit::zeroed`]: std::mem::MaybeUninit::zeroed
    #[cfg(feature = "allocator_api")]
    pub fn new_zeroed_in(len: usize, allocator: A) -> Self {
        // SAFETY: All invariants are upheld by construction.
        unsafe { Self::new(0, len, Allocation::allocate_zeroed_in(len, &allocator), allocator) }
    }

    /// Constructs a new `SliceRwLock` with uninitialized contents in the provided allocator,
    /// returning an error if the allocation fails.
    #[cfg(feature = "allocator_api")]
    pub fn try_new_uninit_in(len: usize, allocator: A) -> Result<Self, AllocError> {
        // SAFETY: All invariants are upheld by construction.
        Allocation::try_allocate_uninit_in(len, &allocator).map(|ptr| unsafe { Self::new(0, len, ptr, allocator) })
    }

    /// Constructs a new `SliceRwLock` with uninitialized contents,
    /// with the memory being filled with `0` bytes, in the provided allocator,
    /// returning an error if the allocation fails.
    ///
    /// See [`MaybeUninit::zeroed`] for examples of correct and incorrect
    /// usage of this method.
    ///
    /// [`Maybeuninit::zeroed`]: std::mem::MaybeUninit::zeroed
    #[cfg(feature = "allocator_api")]
    pub fn try_new_zeroed_in(len: usize, allocator: A) -> Result<Self, AllocError> {
        // SAFETY: All invariants are upheld by construction.
        Allocation::try_allocate_zeroed_in(len, &allocator).map(|ptr| unsafe { Self::new(0, len, ptr, allocator) })
    }

    /// Converts to `SliceRwLock<T, A>` wrapped in `Ok` if `self` is the only guard
    /// to the slice. Otherwise returns `Err` containing the original lock.
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
    pub unsafe fn assume_init(self) -> Result<SliceRwLock<T, A>, Self> {
        if self.is_all() {
            // SAFETY: Checked above that `self` is the only guard to the allocation.
            Ok(unsafe { self.assume_init_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Converts to `SliceRwLock<T, A>`, assuming the caller is the only lock guarding the allocation.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the inner value
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// Calling this while another entity guarding the slice exists
    /// might lead to undefined behaviour when all guards are dropped.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    pub const unsafe fn assume_init_unchecked(self) -> SliceRwLock<T, A> {
        // SAFETY: All fields of `self` are forgotten immediately after
        // reading them out of the pointers.
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
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        // The existance of `self` guarantees that the counter is at least 1.
        // By construction, `allocation` points to live and valid data.
        unsafe {
            Allocation::drop_in_unchecked(self.inner.allocation, &self.allocator);
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

impl<T, const N: usize, A: Allocator> From<ArrayRwLock<T, N, A>> for SliceRwLock<T, A> {
    /// Converts an `ArrayRwLock<T, A>` into a `SliceRwLock<T, A>`.
    fn from(value: ArrayRwLock<T, N, A>) -> Self {
        value.into_slice()
    }
}

impl<T, A: Allocator> From<Box<[T], A>> for SliceRwLock<T, A> {
    /// Converts a `Box<[T], A>` into a `SliceRwLock<T, A>`.
    ///
    /// This conversion allocates on the heap and moves the data.
    fn from(value: Box<[T], A>) -> Self {
        let (ptr, allocator) = Box::into_non_null_with_allocator(value);
        let (ptr, len) = ptr.to_raw_parts();
        let ptr = ptr.cast::<MaybeUninit<T>>();
        let ptr_reallocated = Allocation::<MaybeUninit<T>>::allocate_uninit_in(len, &allocator);
        unsafe {
            // SAFETY: Allocated above.
            let slice_ptr_reallocated = Allocation::get_slice(ptr_reallocated);
            // SAFETY: Both pointers point to live allocations produced by the same
            // allocator, so the data cannot overlap.
            slice_ptr_reallocated
                .to_raw_parts()
                .0
                .cast()
                .copy_from_nonoverlapping(ptr, len);
            // SAFETY: By construction, `ptr` points to an allocation produced by
            // `allocator` with a layout of an array of length `len`.
            allocator.deallocate(ptr.cast(), Layout::array::<T>(len).unwrap_unchecked());
            let (ptr, metadata) = ptr_reallocated.to_raw_parts();
            // SAFETY: All invariants are upheld by construction.
            Self::new(0, len, NonNull::from_raw_parts(ptr, metadata), allocator)
        }
    }
}

impl<T, A: Allocator> From<Vec<T, A>> for SliceRwLock<T, A> {
    /// Converts a `Vec<T, A>` into a `SliceRwLock<T, A>`.
    ///
    /// This conversion allocates on the heap and moves the data.
    ///
    /// # Note
    ///
    /// If the passed `Vec` is not fully populated (i.e., `len != cap`),
    /// this operation will result in two reallocations.
    fn from(value: Vec<T, A>) -> Self {
        value.into_boxed_slice().into()
    }
}
