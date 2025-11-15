use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    iter::FusedIterator,
    num::NonZeroUsize,
    ops::Drop,
    ptr::NonNull,
};

use super::lock::SliceRwLock;
use crate::core::{self, Allocation};

/// An iterator over a `SliceRwLock` in locks to (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the end of the slice.
///
/// When the slice len is not evenly divided by the chunk size, a lock to the last slice
/// of the iteration will be the remainder.
///
/// This struct is created by the [`rchunks`] method on [`SliceRwLock`].
///
/// [`rchunks`]: SliceRwLock::rchunks
#[clippy::has_significant_drop]
pub struct RChunks<T, A: Allocator = Global> {
    chunk_size: NonZeroUsize,
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, A: Allocator> RChunks<T, A> {
    /// Creates a new instance of `RChunks` without checking whether `start + len` overflows.
    /// Does not increment the reference counter.
    ///
    /// # Safety
    /// See [`SliceRwLock::new`]
    #[inline]
    pub(crate) const unsafe fn new_unchecked_not_increment(
        chunk_size: NonZeroUsize,
        start: usize,
        len: usize,
        allocation: NonNull<Allocation<T>>,
        allocator: A,
    ) -> Self {
        debug_assert!(start.checked_add(len).is_some());

        Self {
            chunk_size,
            start,
            // SAFETY: User-upheld invariant.
            end: unsafe { start.unchecked_add(len) },
            allocation,
            allocator,
        }
    }
}

impl<T, A: Allocator> Drop for RChunks<T, A> {
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

impl<T, A: Allocator + Clone> Iterator for RChunks<T, A> {
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);

        // SAFETY: By construction, `start <= end`.
        let len = unsafe { self.end.unchecked_sub(self.start) };
        if self.chunk_size.get() < len {
            unsafe {
                // SAFETY: Checked above that `chunk_size < end - start`, which implies `start < end - chunk_size`.
                self.end = self.end.unchecked_sub(self.chunk_size.get());
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(self.end, self.chunk_size.get(), self.allocation, self.allocator.clone()))
            }
        } else if len > 0 {
            core::cold_path();
            self.end = self.start;
            // SAFETY: All invariants are upheld by construction.
            unsafe { Some(SliceRwLock::new(self.start, len, self.allocation, self.allocator.clone())) }
        } else {
            core::cold_path();
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

        // SAFETY: By construction, `start <= end`.
        let len = unsafe { self.end.unchecked_sub(self.start) };

        match self.chunk_size.get().checked_mul(n) {
            Some(skip) if skip < len => {
                // SAFETY: Checked above that `skip < len`.
                let remainder = unsafe { len.unchecked_sub(skip) };
                if self.chunk_size.get() < remainder {
                    unsafe {
                        // SAFETY: Checked above that `chunk_size < end - start - skip`, which implies `start < end - skip - chunk_size`.
                        self.end = self.end.unchecked_sub(skip).unchecked_sub(self.chunk_size.get());
                        // SAFETY: All invariants are upheld by construction.
                        Some(SliceRwLock::new(self.end, self.chunk_size.get(), self.allocation, self.allocator.clone()))
                    }
                } else {
                    self.end = self.start;
                    // SAFETY: All invariants are upheld by construction.
                    unsafe { Some(SliceRwLock::new(self.start, remainder, self.allocation, self.allocator.clone())) }
                }
            }
            Some(_) => {
                self.end = self.start;
                None
            }
            _ => {
                core::cold_path();
                None
            }
        }
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for RChunks<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);

        // SAFETY: By construction, `start <= end`.
        let len = unsafe { self.end.unchecked_sub(self.start) };
        if self.chunk_size.get() < len {
            let chunk = {
                let tmp = len % self.chunk_size;
                if core::unlikely(tmp == 0) { self.chunk_size.get() } else { tmp }
            };
            let start_old = self.start;
            unsafe {
                // SAFETY: Checked above that `chunk_size < end - start`, which implies
                // `start + len % chunk_size <= start + chunk_size < end`.
                self.start = self.start.unchecked_add(chunk);
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(start_old, chunk, self.allocation, self.allocator.clone()))
            }
        } else if len > 0 {
            core::cold_path();
            let start_old = self.start;
            self.start = self.end;
            // SAFETY: All invariants are upheld by construction.
            unsafe { Some(SliceRwLock::new(start_old, len, self.allocation, self.allocator.clone())) }
        } else {
            core::cold_path();
            None
        }
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RChunks<T, A> {
    #[inline]
    fn len(&self) -> usize {
        // SAFETY: By construction, `start < end`.
        let len = unsafe { self.end.unchecked_sub(self.start) };
        len / self.chunk_size + if len % self.chunk_size == 0 { 0 } else { 1 }
    }
}

impl<T, A: Allocator + Clone> FusedIterator for RChunks<T, A> {}

impl<T, A: Allocator> Debug for RChunks<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RChunks")
            .field("chunk_size", &self.chunk_size)
            .field("start", &self.start)
            .field("end", &self.end)
            .field("allocation", &self.allocation)
            .finish_non_exhaustive()
    }
}
