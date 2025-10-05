use std::{
    alloc::Allocator,
    iter::FusedIterator,
    mem::ManuallyDrop,
    num::NonZeroUsize,
    ops::Drop,
    ptr::NonNull,
};
use crate::inner::{self, alloc::Allocation};
use super::lock::SliceRwLock;


/// An iterator over a `SliceRwlock` in locks to (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the end of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last
/// up to `chunk_size-1` elements will be omitted but can be retrieved from
/// the [`remainder`] function from the iterator.
///
/// This struct is created by the [`rchunks_exact`] method on [`SliceRwLock`].
/// 
/// [`remainder`]: RChunksExact::remainder
/// [`rchunks_exact`]: SliceRwLock::rchunks_exact
#[clippy::has_significant_drop]
pub struct RChunksExact<T, A: Allocator> {
    remainder_start: usize,
    remainder_len: usize,
    chunk_size: NonZeroUsize,
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, A: Allocator> RChunksExact<T, A> {
    /// Creates a new instance of `RChunksExact` without checking whether `start + len` overflows.
    /// Does not increment the atomic counter.
    /// 
    /// # Safety
    /// See [`SliceRwLock::new`]
    #[inline]
    pub(crate) const fn new_unchecked(chunk_size: NonZeroUsize, start: usize, len: usize, allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        // Shenanigans to bypass the `%` operator not being const.
        // SAFETY: `chunk_size` is non-zero.
        let remainder_len = unsafe { len.checked_rem(chunk_size.get()).unwrap_unchecked() };
        Self {
            remainder_start: start,
            remainder_len,
            chunk_size,
            // SAFETY: `start + len % chunk_size <= start + len`.
            // Assuming user-upheld invariant, this cannot overflow.
            start: unsafe { start.unchecked_add(remainder_len) },
            // SAFETY: User-upheld invariant.
            end: unsafe { start.unchecked_add(len) },
            allocation,
            allocator
        }
    }

    /// Returns the a lock to the remainder of the original guarded slice that is not going to be
    /// returned by the iterator. The slice guarded by the returned lock has at most `chunk_size-1`
    /// elements.
    #[inline]
    pub fn remainder(self) -> SliceRwLock<T, A> {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            SliceRwLock::new_not_incremented(
                orig.remainder_start, 
                orig.remainder_len, 
                orig.allocation, 
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&orig.allocator as *const A).read()
            )
        }
    }
}

impl<T, A: Allocator> Drop for RChunksExact<T, A> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(unsafe { Allocation::get_metadata_disjoint(self.allocation).state.get_counter() } > 0);

        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        // The existance of `self` guarantees that the counter is at least 1.
        // By construction, `allocation` points to live and valid data.
        unsafe { Allocation::drop_in_unchecked(self.allocation, &self.allocator); }
    }
}

impl<T, A: Allocator + Clone> Iterator for RChunksExact<T, A> {
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);
        debug_assert!((self.end - self.start) % self.chunk_size == 0);

        if self.start < self.end {
            unsafe {
                // SAFETY: By construction, `end - start` is a multiple of `chunk_size`.
                // Checked above that `start < end`, so they must be at least `chunks_size` apart.
                self.end = self.end.unchecked_sub(self.chunk_size.get());
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(self.end, self.chunk_size.get(), self.allocation, self.allocator.clone()))
            }
        } else {
            inner::cold_path();
            None
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);
        debug_assert!((self.end - self.start) % self.chunk_size == 0);

        // SAFETY: By construction, `start < end`.
        let len = unsafe { self.end.unchecked_sub(self.start) };
        match self.chunk_size.get().checked_mul(n) {
            Some(skip) if skip < len => unsafe {
                // SAFETY: Checked above that `n * chunk_size < end - start`. This implies
                // `start < end - n * chunk_size`. By construction, `end - start` is a multiple
                // of `chunk_size`, so `start` and `end - n * chunk_size` must be at least `chunk_size` apart.
                self.end = self.end.unchecked_sub(skip).unchecked_sub(self.chunk_size.get());
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(self.end, self.chunk_size.get(), self.allocation, self.allocator.clone()))
            },
            Some(_) => {
                self.start = self.end;
                None
            },
            _ => { inner::cold_path(); None }
        }
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for RChunksExact<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);
        debug_assert!((self.end - self.start) % self.chunk_size == 0);

        if self.start < self.end {
            let start_old = self.start;
            unsafe {
                // SAFETY: By construction, `end - start` is a multiple of `chunk_size`.
                // Checked above that `start < end`, so they must be at least `chunks_size` apart.
                self.start = self.start.unchecked_add(self.chunk_size.get());
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(start_old, self.chunk_size.get(), self.allocation, self.allocator.clone()))
            }
        } else {
            inner::cold_path();
            None
        }
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RChunksExact<T, A> {
    fn len(&self) -> usize {
        debug_assert!(self.start <= self.end);

        // SAFETY: By construction, `start < end`.
        unsafe { self.end.unchecked_sub(self.start) / self.chunk_size }
    }
}

impl<T, A: Allocator + Clone> FusedIterator for RChunksExact<T, A> {}
