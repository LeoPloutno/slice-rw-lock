use super::{read_all::ArrayRwLockReadAllGuard, write::ArrayRwLockWriteGuard, write_all::ArrayRwLockWriteAllGuard};
use crate::{
    core::{Allocation, State},
    element::lock::ElementRwLock,
    slice::lock::SliceRwLock,
};
use std::{
    alloc::{Allocator, Global, Layout},
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    ops::Range,
    panic::{RefUnwindSafe, UnwindSafe},
    process,
    ptr::NonNull,
    sync::{LockResult, PoisonError, TryLockError, TryLockResult, atomic::Ordering},
};

pub(super) struct InnerArrayRwLock<T> {
    pub(super) start: usize,
    pub(super) allocation: NonNull<Allocation<T>>,
}

#[clippy::has_significant_drop]
pub struct ArrayRwLock<T, const N: usize, A: Allocator = Global> {
    pub(super) inner: InnerArrayRwLock<T>,
    allocator: A,
}

impl<T, const N: usize, A: Allocator> ArrayRwLock<T, N, A> {
    /// Creates a new lock to the underlying `allocation` without incrementing the reference counter.
    ///
    /// # Safety
    /// * `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// * `start` must index an element inside the array pointed to by `allocation`.
    /// * `start + N` must either index an element of said array or point one element past its end.
    /// * The reference counter must not be zero when this function is called.
    #[inline]
    pub(crate) const unsafe fn new_not_incremented(start: usize, allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        Self {
            allocator,
            inner: InnerArrayRwLock { start, allocation },
        }
    }

    /// Creates a new lock to the underlying `allocation`. Atomically increments the reference counter.
    ///
    /// # Safety
    /// * `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// * `start` must index an element inside the array pointed to by `allocation`.
    /// * `start + N` must either index an element of said array or point one element past its end.
    pub(crate) unsafe fn new(start: usize, allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        if unsafe {
            Allocation::get_metadata_disjoint(allocation)
                .state
                .fetch_increment_counter_unchecked(Ordering::Release)
        } == State::MAX_COUNT
        {
            process::abort();
        }
        // SAFETY: User-upheld invariants.
        unsafe { Self::new_not_incremented(start, allocation, allocator) }
    }

    /// Returns a lock to the entire slice wrapped in `Ok` if `self` is the only
    /// entity guarding the slice. Otherwise, returns `Err` containing the original lock.
    pub fn into_all(self) -> Result<SliceRwLock<T, A>, Self> {
        // SAFETY: By construction, `allocation` points to live amd valid data.
        if self.is_all() {
            let orig = ManuallyDrop::new(self);
            Ok(unsafe {
                // SAFETY: All invariants are upheld by construction.
                SliceRwLock::new_not_incremented(
                    0,
                    // SAFETY: By construction, `allocation` points to live amd valid data.
                    Allocation::len(orig.inner.allocation),
                    orig.inner.allocation,
                    // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                    (&raw const orig.allocator).read(),
                )
            })
        } else {
            Err(self)
        }
    }

    /// Returns a lock to a slice containing the entire array.
    pub const fn into_slice(self) -> SliceRwLock<T, A> {
        let ret = unsafe {
            // SAFETY: All invariants are upheld by construction.
            SliceRwLock::new_not_incremented(
                self.inner.start,
                N,
                self.inner.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten below.
                (&self.allocator as *const A).read(),
            )
        };
        mem::forget(self);
        ret
    }

    /// Locks the allocation guarded by this 'ArrayRwLock' with shared global read access, blocking
    /// the current thread until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more chunk nor global writers which
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
    /// This function will return an error if the `ArrayRwLock` is poisoned. An
    /// `ArrayRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired. The acquired lock guard will be contained in the returned
    /// error.
    pub fn read_all(&self) -> LockResult<ArrayRwLockReadAllGuard<'_, T, N>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.read_whole();
        let guard = ArrayRwLockReadAllGuard(&self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to acquire this `ArrayRwLock` with shared global read access.
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
    /// This function will return the [`Poisoned`] error if the `ArrayRwLock` is
    /// poisoned. An `ArrayRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ArrayRwLock` could
    /// not be acquired because it was already locked exclusively.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_read_all(&self) -> TryLockResult<ArrayRwLockReadAllGuard<'_, T, N>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_read_whole() {
            let guard = ArrayRwLockReadAllGuard(&self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the chunk guarded by this `ArrayRwLock` with exclusive subfield write access, blocking the current
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
    /// This function will return an error if the `ArrayRwLock` is poisoned. An
    /// `ArrayRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write(&mut self) -> LockResult<ArrayRwLockWriteGuard<'_, T, N>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write_subfield();
        let guard = ArrayRwLockWriteGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `ArrayRwLock` with exclusive subfield write access.
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
    /// This function will return the [`Poisoned`] error if the `ArrayRwLock` is
    /// poisoned. An `ArrayRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ArrayRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write(&mut self) -> TryLockResult<ArrayRwLockWriteGuard<'_, T, N>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write_subfield() {
            let guard = ArrayRwLockWriteGuard(&mut self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the allocation guarded by this `ArrayRwLock` with exclusive global write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other writers or other readers
    /// currently have access to the lock.
    ///
    /// Returns an RAII guard which will release this thread's exclusive access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ArrayRwLock` is poisoned. An
    /// `ArrayRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    pub fn write_all(&mut self) -> LockResult<ArrayRwLockWriteAllGuard<'_, T, N>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write_whole();
        let guard = ArrayRwLockWriteAllGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `ArrayRwLock` with exclusive global write access.
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
    /// This function will return the [`Poisoned`] error if the `ArrayRwLock` is
    /// poisoned. An `ArrayRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ArrayRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write_all(&mut self) -> TryLockResult<ArrayRwLockWriteAllGuard<'_, T, N>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write_whole() {
            let guard = ArrayRwLockWriteAllGuard(&mut self.inner, PhantomData);
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
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }.state.clear_poison();
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
            // SAFETY: By construction, `start + N` points within or right outside the allocation.
            end: unsafe { self.inner.start.unchecked_add(N) },
        }
    }
}

impl<T, const N: usize, A: Allocator + Clone> ArrayRwLock<T, N, A> {
    /// Converts a lock to an array into an array of locks to elements
    pub fn each(self) -> [ElementRwLock<T, A>; N] {
        let mut array = [const { MaybeUninit::<ElementRwLock<T, A>>::uninit() }; N];
        for (i, item) in array.iter_mut().enumerate() {
            item.write(unsafe {
                // SAFETY: All invariants are upheld by construction.
                ElementRwLock::new(
                    // SAFETY: By construction, `start + N` points within or right outside the allocation.
                    // By construction, `i < N`.
                    self.inner.start.unchecked_add(i),
                    self.inner.allocation,
                    self.allocator.clone(),
                )
            });
        }
        let ret = unsafe { mem::transmute_copy(&array) };
        mem::forget(array);
        ret
        // array::from_fn(|i| unsafe {
        //     // SAFETY: All invariants are upheld by construction.
        //     ElementRwLock::new(
        //         // SAFETY: By construction, `start + N` points within or right outside the allocation.
        //         // By construction, `i < N`.
        //         self.inner.start.unchecked_add(i),
        //         self.inner.allocation,
        //         self.allocator.clone(),
        //     )
        // })
    }

    /// Divides one lock guarding an array into two at an index.
    ///
    /// The first will contain all indices from `[0, M)` (excluding
    /// the index `M` itself) and the second will contain all
    /// indices from `[M, N)` (excluding the index `N` itself).
    ///
    /// # Panics
    ///
    /// Panics if `M > N`.
    #[cfg(feature = "split_array")]
    pub fn split_array<const M: usize>(self) -> (ArrayRwLock<T, M, A>, SliceRwLock<T, A>) {
        assert!(M <= N, "`M` must not exceed `N`");

        let orig = ManuallyDrop::new(self);
        unsafe {
            (
                // SAFETY: All invariants are upheld by cpnstruction.
                ArrayRwLock::new(orig.inner.start, orig.inner.allocation, orig.allocator.clone()),
                // SAFETY: All invariants are upheld by cpnstruction.
                SliceRwLock::new(
                    // SAFETY: By construction, `start + N` points within or right outside the allocation.
                    // Checked above that `M <= N`.
                    orig.inner.start.unchecked_add(M),
                    // SAFETY: Checked above that `M <= N`.
                    N.unchecked_sub(M),
                    orig.inner.allocation,
                    // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                    (&raw const orig.allocator).read(),
                ),
            )
        }
    }

    /// Divides one lock guarding an array into two at an index.
    ///
    /// The first will contain all indices from `[0, N - M)` (excluding
    /// the index `N - M` itself) and the second will contain all
    /// indices from `[N - M, N)` (excluding the index `N` itself).
    ///
    /// # Panics
    ///
    /// Panics if `M > N`.
    #[cfg(feature = "split_array")]
    pub fn rsplit_array<const M: usize>(self) -> (SliceRwLock<T, A>, ArrayRwLock<T, M, A>) {
        assert!(M <= N, "`M` must not exceed `N`");

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: Checked above that `M <= N`.
            let slice_len = N.unchecked_sub(M);
            (
                // SAFETY: All invariants are upheld by cpnstruction.
                SliceRwLock::new(orig.inner.start, slice_len, orig.inner.allocation, orig.allocator.clone()),
                // SAFETY: All invariants are upheld by cpnstruction.
                ArrayRwLock::new(
                    // SAFETY: By construction, `start + N` points within or right outside the allocation.
                    // Checked above that `M <= N`, which implies `0 <= start + N - M`
                    orig.inner.start.unchecked_add(slice_len),
                    orig.inner.allocation,
                    // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                    (&raw const orig.allocator).read(),
                ),
            )
        }
    }
}

impl<T, const N: usize, A: Allocator> ArrayRwLock<MaybeUninit<T>, N, A> {
    /// Converts to `ArrayRwLock<T, A>`.
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
    pub const unsafe fn assume_init(self) -> ArrayRwLock<T, N, A> {
        // SAFETY: All fields of `self` are forgotten immediately after
        // reading them out of the pointers.
        let allocator = unsafe { (&raw const self.allocator).read() };
        let inner = unsafe { (&raw const self.inner).read() };
        mem::forget(self);

        let (ptr, len) = inner.allocation.to_raw_parts();
        ArrayRwLock {
            allocator,
            inner: InnerArrayRwLock {
                start: inner.start,
                allocation: NonNull::from_raw_parts(ptr, len),
            },
        }
    }
}

impl<T, const N: usize, A: Allocator> Drop for ArrayRwLock<T, N, A> {
    fn drop(&mut self) {
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        // The existance of `self` guarantees that the counter is at least 1.
        // By construction, `allocation` points to live and valid data.
        unsafe {
            Allocation::drop_in_unchecked(self.inner.allocation, &self.allocator);
        }
    }
}

impl<T: Debug, const N: usize, A: Allocator> Debug for ArrayRwLock<T, N, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("ArrayRwLock");
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
        d.field("poisoned", &self.is_poisoned());
        d.finish_non_exhaustive()
    }
}

unsafe impl<T: Send + Sync, const N: usize, A: Allocator> Send for ArrayRwLock<T, N, A> {}

impl<T, const N: usize, A: Allocator> RefUnwindSafe for ArrayRwLock<T, N, A> {}

impl<T, const N: usize, A: Allocator> UnwindSafe for ArrayRwLock<T, N, A> {}

impl<T, const N: usize, A: Allocator> TryFrom<SliceRwLock<T, A>> for ArrayRwLock<T, N, A> {
    type Error = SliceRwLock<T, A>;

    fn try_from(value: SliceRwLock<T, A>) -> Result<Self, Self::Error> {
        value.into_array_internal()
    }
}

impl<T, const N: usize, A: Allocator> From<Box<[T; N], A>> for ArrayRwLock<T, N, A> {
    fn from(value: Box<[T; N], A>) -> Self {
        let (ptr, allocator) = Box::into_non_null_with_allocator(value);
        let ptr = ptr.cast::<MaybeUninit<T>>();
        let ptr_reallocated = Allocation::<MaybeUninit<T>>::allocate_uninit_in(N, &allocator);
        unsafe {
            // SAFETY: Allocated above.
            let slice_ptr_reallocated = Allocation::get_data_non_null(ptr_reallocated);
            // SAFETY: Both pointers point to live allocations produced by the same
            // allocator, so the data cannot overlap.
            slice_ptr_reallocated.to_raw_parts().0.cast().copy_from_nonoverlapping(ptr, N);
            // SAFETY: By construction, `ptr` points to an allocation produced by `allocator`.
            allocator.deallocate(ptr.cast(), Layout::new::<[T; N]>());
            let (ptr, metadata) = ptr_reallocated.to_raw_parts();
            // SAFETY: All invariants are upheld by construction.
            Self::new(0, NonNull::from_raw_parts(ptr, metadata), allocator)
        }
    }
}
