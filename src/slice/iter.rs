use std::{
    alloc::Allocator,
    iter::FusedIterator,
    mem::ManuallyDrop,
    ops::Drop,
    ptr::NonNull,
    sync::atomic::{self, Ordering},
};

use crate::{
    ElemRwLock,
    inner::alloc::Allocation,
    slice::lock::{InnerSliceRwLock, SliceRwLock},
};

/// Element lock iterator.
/// 
/// This struct is created by the [`iter`] method on [`SliceRwLock`]
/// 
/// [`iter`]: SliceRwLock::iter
#[clippy::has_significant_drop]
pub struct Iter<T, A: Allocator> {
    pub(crate) start: usize,
    pub(crate) len: usize,
    pub(crate) allocation: NonNull<Allocation<T>>,
    pub(crate) allocator: A,
}

impl<T, A: Allocator> Iter<T, A> {
    /// Converts into a guard to the underlying data.
    pub fn into_slice_rw_lock(self) -> SliceRwLock<T, A> {
        let orig = ManuallyDrop::new(self);
        SliceRwLock {
            inner: InnerSliceRwLock {
                start: orig.start,
                len: orig.len,
                allocation: orig.allocation,
            },
            // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function
            allocator: unsafe { (&orig.allocator as *const A).read() },
        }
    }
}

impl<T, A: Allocator> Drop for Iter<T, A> {
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

impl<T, A: Allocator + Clone> Iterator for Iter<T, A> {
    type Item = ElemRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            let start = self.start;
            unsafe {
                // SAFETY: `self.start + self.len` is guaranteed to point within or right outside the allocation
                self.start = self.start.unchecked_add(1);
                // SAFETY: Checked above that `self.len` is greater than zero
                self.len = self.len.unchecked_sub(1);
                // SAFETY: `self.allocation` points to a live and valid allocation by construction
                Some(ElemRwLock::new(start, self.allocation, self.allocator.clone()))
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
            let start = self.start;
            unsafe {
                // SAFETY: `self.start + self.len` is guaranteed to point within or right outside the allocation.
                // Checked above that `self.len` is greater than `n`
                self.start = self.start.unchecked_add(n + 1);
                // SAFETY: Checked above that `self.len` is greater than `n`
                self.len = self.len.unchecked_sub(n + 1);
                Some(
                    // SAFETY: `self.allocation` points to a live and valid allocation by construction
                    ElemRwLock::new(
                        // SAFETY: `self.start + self.len` is guaranteed to point within or right outside the allocation.
                        // Checked above that `self.len` is greater than `n`
                        start.unchecked_add(n),
                        self.allocation,
                        self.allocator.clone(),
                    ),
                )
            }
        } else {
            self.len = 0;
            None
        }
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for Iter<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            unsafe {
                // SAFETY: Checked above that `self.len` is greater than zero
                self.len = self.len.unchecked_sub(1);
                Some(
                    // SAFETY: `self.allocation` points to a live and valid allocation by construction.
                    ElemRwLock::new(
                        // SAFETY: `self.start + self.len` is guaranteed to point within or right outside the allocation.
                        self.start.unchecked_add(self.len),
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

impl<T, A: Allocator + Clone> ExactSizeIterator for Iter<T, A> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T, A: Allocator + Clone> FusedIterator for Iter<T, A> {}
