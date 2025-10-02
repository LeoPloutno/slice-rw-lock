use std::{
    alloc::Allocator,
    iter::FusedIterator,
    num::NonZeroUsize,
    ops::Drop,
    ptr::NonNull,
    sync::atomic::{self, Ordering},
};

use crate::{inner::alloc::Allocation, slice::lock::SliceRwLock};


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
pub struct RChunks<T, A: Allocator> {
    pub(crate) chunk_size: NonZeroUsize,
    pub(crate) end: usize,
    pub(crate) remainder: usize,
    pub(crate) allocation: NonNull<Allocation<T>>,
    pub(crate) allocator: A,
}

impl<T, A: Allocator> Drop for RChunks<T, A> {
    fn drop(&mut self) {
        // SAFETY: The counter is guaranteed to be at least `1` because
        // when `self` was constructed, it was non-zero
        if unsafe {
            Allocation::get_metadata_disjoint(self.allocation)
                .state
                .fetch_decrement_counter_unchecked(Ordering::Release)
        } == 1
        {
            atomic::compiler_fence(Ordering::Acquire);
            unsafe {
                Allocation::deallocate_in(self.allocation, &self.allocator);
            }
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for RChunks<T, A> {
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remainder >= self.chunk_size.get() {
            unsafe {
                // SAFETY: `self.end - self.remainder` is guaranteed to point within the allocation.
                // Checked above that `self.remainder` is greater than or equal to `self.chunk_size`
                self.end = self.end.unchecked_sub(self.chunk_size.get());
                self.remainder = self.remainder.unchecked_sub(self.chunk_size.get());
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                Some(SliceRwLock::new(
                    self.end,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
            }
        } else if self.remainder > 0 {
            // SAFETY: `self.end - self.remainder` is guaranteed to point within the allocation
            unsafe {
                self.end = self.end.unchecked_sub(self.remainder);
            }
            let remainder = self.remainder;
            self.remainder = 0;
            // SAFETY: `self.allocation` points to a live and valid allocation by construction
            Some(unsafe { SliceRwLock::new(self.end, remainder, self.allocation, self.allocator.clone()) })
        } else {
            None
        }
    }

    fn count(self) -> usize {
        self.len()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let step = n * self.chunk_size.get();
        if self.remainder >= step + self.chunk_size.get() {
            // SAFETY: Checked above that this operation does not overflow
            let leap = unsafe { step.unchecked_add(self.chunk_size.get()) };
            unsafe {
                // SAFETY: `self.end - self.remainder` is guaranteed to point within the allocation.
                // Checked above that `self.remainder` is greater than `step + self.chunk_size`, which is also `leap`
                self.end = self.end.unchecked_sub(leap);
                self.remainder = self.remainder.unchecked_sub(leap);
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                Some(SliceRwLock::new(
                    self.end,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
            }
        } else if self.remainder > step {
            let remainder = self.remainder;
            self.remainder = 0;
            Some(unsafe {
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                SliceRwLock::new(
                    // SAFETY: `self.end - self.remainder` is guaranteed to point within the allocation
                    self.end.unchecked_sub(remainder),
                    // SAFETY: Checked above that `self.remainder` is greater than `step`
                    remainder.unchecked_sub(step),
                    self.allocation,
                    self.allocator.clone(),
                )
            })
        } else {
            self.remainder = 0;
            None
        }
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for RChunks<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remainder == 0 {
            None
        } else {
            let tmp = self.remainder % self.chunk_size;
            let chunk_size = if tmp == 0 { self.chunk_size.get() } else { tmp };
            let remainder = self.remainder;
            unsafe {
                // SAFETY: `chunk_size` is guaranteed to be smaller than `self.remainder` by construction
                self.remainder = self.remainder.unchecked_sub(chunk_size);
                Some(
                    // SAFETY: `self.allocation` points to a live and valid allocation by construction
                    SliceRwLock::new(
                        // SAFETY: `self.end - self.remainder` is guaranteed to point within the allocation
                        self.end.unchecked_sub(remainder),
                        chunk_size,
                        self.allocation,
                        self.allocator.clone(),
                    ),
                )
            }
        }
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RChunks<T, A> {
    fn len(&self) -> usize {
        self.remainder / self.chunk_size + if self.remainder % self.chunk_size == 0 { 0 } else { 1 }
    }
}

impl<T, A: Allocator + Clone> FusedIterator for RChunks<T, A> {}
