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
/// time), starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the chunk size, a lock to the last slice
/// of the iteration will be the remainder.
///
/// This struct is created by the [`chunks`] method on [`SliceRwLock`].
/// 
/// [`chunks`]: SliceRwLock::chunks
#[clippy::has_significant_drop]
pub struct Chunks<T, A: Allocator> {
    pub(crate) chunk_size: NonZeroUsize,
    pub(crate) start: usize,
    pub(crate) remainder: usize,
    pub(crate) allocation: NonNull<Allocation<T>>,
    pub(crate) allocator: A,
}

impl<T, A: Allocator> Drop for Chunks<T, A> {
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

impl<T, A: Allocator + Clone> Iterator for Chunks<T, A> {
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remainder >= self.chunk_size.get() {
            let start = self.start;
            unsafe {
                // SAFETY: `self.start + self.remainder` is guaranteed to point within or right outside the allocation.
                // Checked above that `self.remainder` is greater than or equal to `self.chunk_size`
                self.start = self.start.unchecked_add(self.chunk_size.get());
                // SAFETY: Checked above that `self.remainder` is greater than or equal to `self.chunk_size`
                self.remainder = self.remainder.unchecked_sub(self.chunk_size.get());
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                Some(SliceRwLock::new(
                    start,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
            }
        } else if self.remainder > 0 {
            let remainder = self.remainder;
            self.remainder = 0;
            // SAFETY: `self.allocation` points to a live and valid allocation by construction
            Some(unsafe { SliceRwLock::new(self.start, remainder, self.allocation, self.allocator.clone()) })
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
            let start = self.start;
            unsafe {
                // SAFETY: Checked above that this operation does not overflow
                let leap = step.unchecked_add(self.chunk_size.get());
                // SAFETY: `self.start + self.remainder` is guaranteed to point within or right outside the allocation.
                // Checked above that `self.remainder` is greater than or equal to `step + self.chunk_size`
                self.start = self.start.unchecked_add(leap);
                // SAFETY: Checked above that `self.remainder` is greater than or equal to `step + self.chunk_size`
                self.remainder = self.remainder.unchecked_add(leap);
                Some(
                    // SAFETY: `self.allocation` points to a live and valid allocation by construction
                    SliceRwLock::new(
                        // SAFETY: `self.start + self.remainder` is guaranteed to point within or right outside the allocation.
                        // Checked above that `self.remainder` is greater than `step`
                        start.unchecked_add(step),
                        self.chunk_size.get(),
                        self.allocation,
                        self.allocator.clone(),
                    )
                )
            }
        } else if self.remainder > step {
            let remainder = self.remainder;
            self.remainder = 0;
            Some(unsafe {
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                SliceRwLock::new(
                    // SAFETY: `self.start + self.remainder` is guaranteed to point within or right outside the allocation.
                    // Checked above that `self.remainder` is greater than `step`
                    self.start.unchecked_add(step),
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

impl<T, A: Allocator + Clone> DoubleEndedIterator for Chunks<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remainder == 0 {
            None
        } else {
            let tmp = self.remainder % self.chunk_size;
            if tmp == 0 {
                unsafe {
                    // SAFETY: Checked above that `self.remainder` is greater than or equal to `self.chunk_size`
                    self.remainder = self.remainder.unchecked_sub(self.chunk_size.get());
                    Some(
                        // SAFETY: `self.allocation` points to a live and valid allocation by construction
                        SliceRwLock::new(
                            // SAFETY: `self.start + self.remainder` is guaranteed to point within or right outside the allocation
                            self.start.unchecked_add(self.remainder),
                            self.chunk_size.get(),
                            self.allocation,
                            self.allocator.clone(),
                        ),
                    )
                }
            } else {
                unsafe {
                    // SAFETY: A modulo operation cannot return something larger than its first operand
                    self.remainder = self.remainder.unchecked_sub(tmp);
                    Some(
                        // SAFETY: `self.allocation` points to a live and valid allocation by construction
                        SliceRwLock::new(
                            // SAFETY: `self.start + self.remainder` is guaranteed to point within or right outside the allocation
                            self.start.unchecked_add(self.remainder),
                            tmp,
                            self.allocation,
                            self.allocator.clone(),
                        ),
                    )
                }
            }
        }
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for Chunks<T, A> {
    fn len(&self) -> usize {
        self.remainder / self.chunk_size + if self.remainder % self.chunk_size == 0 { 0 } else { 1 }
    }
}

impl<T, A: Allocator + Clone> FusedIterator for Chunks<T, A> {}
