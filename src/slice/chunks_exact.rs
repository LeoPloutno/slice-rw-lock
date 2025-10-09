use super::lock::SliceRwLock;
use crate::inner::{self, alloc::Allocation};
use std::{alloc::Allocator, iter::FusedIterator, mem::ManuallyDrop, num::NonZeroUsize, ops::Drop, ptr::NonNull};

/// An iterator over a `SliceRwlock` in locks to (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last
/// up to `chunk_size-1` elements will be omitted but can be retrieved from
/// the [`remainder`] function from the iterator.
///
/// This struct is created by the [`chunks_exact`] method on [`SliceRwLock`].
///
/// [`remainder`]: ChunksExact::remainder
/// [`chunks_exact`]: SliceRwLock::chunks_exact
#[clippy::has_significant_drop]
pub struct ChunksExact<T, A: Allocator> {
    remainder_start: usize,
    remainder_len: usize,
    chunk_size: NonZeroUsize,
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, A: Allocator> ChunksExact<T, A> {
    /// Creates a new instance of `ChunksExact` without checking whether `start + len` overflows.
    /// Does not increment the atomic counter.
    ///
    /// # Safety
    /// See [`SliceRwLock::new`]
    #[inline]
    pub(crate) const fn new_unchecked_not_increment(
        chunk_size: NonZeroUsize,
        start: usize,
        len: usize,
        allocation: NonNull<Allocation<T>>,
        allocator: A,
    ) -> Self {
        // Shenanigans to bypass the `%` operator not being const.
        // SAFETY: `chunk_size` is non-zero.
        let remainder_len = unsafe { len.checked_rem(chunk_size.get()).unwrap_unchecked() };
        // SAFETY: `start <= start + len - len % chunk_size < start + len`.
        // Assuming user-upheld invariant, this cannot overflow.
        let end = unsafe { start.unchecked_add(len).unchecked_sub(remainder_len) };
        Self {
            remainder_start: end,
            remainder_len,
            chunk_size,
            start,
            end,
            allocation,
            allocator,
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
                (&raw const orig.allocator).read(),
            )
        }
    }
}

impl<T, A: Allocator> Drop for ChunksExact<T, A> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(unsafe { Allocation::get_metadata_disjoint(self.allocation).state.get_counter() } > 0);

        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        // The existance of `self` guarantees that the counter is at least 1.
        // By construction, `allocation` points to live and valid data.
        unsafe {
            Allocation::drop_in_unchecked(self.allocation, &self.allocator);
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for ChunksExact<T, A> {
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);
        debug_assert!((self.end - self.start) % self.chunk_size == 0);

        if self.start < self.end {
            let start = self.start;
            unsafe {
                // SAFETY: By construction, `end - start` is a multiple of `chunk_size`.
                // Checked above that `start < end`, so they must be at least `chunks_size` apart.
                self.start = self.start.unchecked_add(self.chunk_size.get());
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(
                    start,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
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
                // SAFETY: Checked above that `skip < end - start`, which implies `start + skip < end`
                let start = self.start.unchecked_add(skip);
                // SAFETY: Checked above that `n * chunk_size < end - start`. This implies
                // `start + n * chunk_size < end`. By construction, `end - start` is a multiple
                // of `chunk_size`, so `start + n * chunk_size` and `end` must be at least `chunk_size` apart.
                self.start = start.unchecked_add(self.chunk_size.get());
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(
                    start,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
            },
            Some(_) => {
                self.start = self.end;
                None
            }
            _ => {
                inner::cold_path();
                None
            }
        }
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for ChunksExact<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);
        debug_assert!((self.end - self.start) % self.chunk_size == 0);

        if self.start < self.end {
            unsafe {
                // SAFETY: By construction, `end - start` is a multiple of `chunk_size`.
                // Checked above that `start < end`, so they must be at least `chunks_size` apart.
                self.end = self.end.unchecked_sub(self.chunk_size.get());
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(
                    self.end,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
            }
        } else {
            inner::cold_path();
            None
        }
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for ChunksExact<T, A> {
    fn len(&self) -> usize {
        debug_assert!(self.start <= self.end);

        // SAFETY: By construction, `start < end`.
        unsafe { self.end.unchecked_sub(self.start) / self.chunk_size }
    }
}

impl<T, A: Allocator + Clone> FusedIterator for ChunksExact<T, A> {}
