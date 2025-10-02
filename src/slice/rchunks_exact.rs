use std::{
    alloc::Allocator,
    iter::FusedIterator,
    mem::ManuallyDrop,
    num::NonZeroUsize,
    ops::Drop,
    ptr::NonNull,
    sync::atomic::{self, Ordering},
};

use crate::{
    inner::alloc::Allocation,
    slice::lock::{InnerSliceRwLock, SliceRwLock},
};

pub(crate) struct Chunk {
    pub(crate) start: usize,
    pub(crate) len: usize,
}

/// An iterator over a `SliceRwlock` in locks to (non-overlapping) chunks (`chunk_size` elements at a
/// time), starting at the end of the slice.
///
/// When the slice len is not evenly divided by the chunk size, the last
/// up to `chunk_size-1` elements will be omitted but can be retrieved from
/// the [`remainder`] function from the iterator.
///
/// This struct is created by the [`chunks_exact`] method on [`SliceRwLock`].
/// 
/// [`remainder`]: RChunksExact::remainder
/// [`chunks_exact`]: SliceRwLock::rchunks_exact
#[clippy::has_significant_drop]
pub struct RChunksExact<T, A: Allocator> {
    pub(crate) chunk_size: NonZeroUsize,
    pub(crate) end: usize,
    pub(crate) len: usize,
    pub(crate) remainder: Chunk,
    pub(crate) allocation: NonNull<Allocation<T>>,
    pub(crate) allocator: A,
}

impl<T, A: Allocator> RChunksExact<T, A> {
    /// Returns the a lock to the remainder of the original guarded slice that is not going to be
    /// returned by the iterator. The slice guarded by the returned lock has at most `chunk_size-1`
    /// elements.
    pub fn remainder(self) -> SliceRwLock<T, A> {
        let orig = ManuallyDrop::new(self);
        // SAFETY: `self.allocation` points to a live and valid allocation by construction
        SliceRwLock {
            inner: InnerSliceRwLock {
                start: orig.remainder.start,
                len: orig.remainder.len,
                allocation: orig.allocation,
            },
            // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
            allocator: unsafe { (&orig.allocator as *const A).read() },
        }
    }
}

impl<T, A: Allocator> Drop for RChunksExact<T, A> {
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

impl<T, A: Allocator + Clone> Iterator for RChunksExact<T, A> {
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            unsafe {
                // SAFETY: `self.end - self.len * self.chunk_size` is guaranteed to point within the allocation
                self.end = self.end.unchecked_add(self.chunk_size.get());
                // SAFETY: Checked above that `self.len` is greater than zero
                self.len = self.len.unchecked_sub(1);
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                Some(SliceRwLock::new(
                    self.end,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
            }
        } else {
            None
        }
    }

    fn count(self) -> usize {
        self.len
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.len > n {
            unsafe {
                // SAFETY: Checked above that `self.len > n` (equivalently, `self.len >= n + 1`), hence
                // `self.end - self.len * self.chunk_size <= self.end - (n + 1) * self.chunk_size`
                self.end = self.end.unchecked_sub(n.unchecked_add(1).unchecked_mul(self.chunk_size.get()));
                // SAFETY: Checked above that `self.len` is greater than `n`
                self.len = self.len.unchecked_sub(n.unchecked_add(1));
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                Some(SliceRwLock::new(
                    self.end,
                    self.chunk_size.get(),
                    self.allocation,
                    self.allocator.clone(),
                ))
            }
        } else {
            None
        }
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for RChunksExact<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            let len = self.len;
            unsafe {
                // SAFETY: Checked above that `self.len` is greater than zero
                self.len = self.len.unchecked_sub(1);
                Some(
                    // SAFETY: `self.allocation` points to a live and valid allocation by construction
                    SliceRwLock::new(
                        // SAFETY: `self.end - self.len * self.chunk_size` is guaranteed to point within or right outside the allocation
                        self.end.unchecked_sub(len.unchecked_mul(self.chunk_size.get())),
                        self.chunk_size.get(),
                        self.allocation,
                        self.allocator.clone(),
                    ),
                )
            }
        } else {
            None
        }
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RChunksExact<T, A> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T, A: Allocator + Clone> FusedIterator for RChunksExact<T, A> {}
