use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    iter::FusedIterator,
    mem::ManuallyDrop,
    ops::Drop,
    ptr::NonNull,
};

use super::lock::SliceRwLock;
use crate::{
    ElementRwLock,
    inner::{self, Allocation},
};

/// Element lock iterator.
///
/// This struct is created by the [`iter`] method on [`SliceRwLock`]
///
/// [`iter`]: SliceRwLock::iter
#[clippy::has_significant_drop]
pub struct Iter<T, A: Allocator = Global> {
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, A: Allocator> Iter<T, A> {
    /// Creates a new instance of `Iter` without checking whether `start + len` overflows.
    /// Does not increment the reference counter.
    ///
    /// # Safety
    /// See [`SliceRwLock::new`]
    #[inline]
    pub(crate) const unsafe fn new_unchecked_not_increment(
        start: usize,
        len: usize,
        allocation: NonNull<Allocation<T>>,
        allocator: A,
    ) -> Self {
        debug_assert!(start.checked_add(len).is_some());

        Self {
            start,
            // SAFETY: User-upheld invariant.
            end: unsafe { start.unchecked_add(len) },
            allocation,
            allocator,
        }
    }

    /// Converts into a guard to the underlying data.
    pub fn into_slice(self) -> SliceRwLock<T, A> {
        debug_assert!(self.start <= self.end);

        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            SliceRwLock::new_not_incremented(
                orig.start,
                // SAFETY: By construction, `start <= end`.
                orig.end.unchecked_sub(orig.start),
                orig.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&raw const orig.allocator).read(),
            )
        }
    }
}

impl<T, A: Allocator> Drop for Iter<T, A> {
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

impl<T, A: Allocator + Clone> Iterator for Iter<T, A> {
    type Item = ElementRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let start_old = self.start;
            unsafe {
                // SAFETY: Checked above that `start < end`.
                self.start = self.start.unchecked_add(1);
                // SAFETY: All invariants are upheld by construction.
                Some(ElementRwLock::new(start_old, self.allocation, self.allocator.clone()))
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
        if n < self.len() {
            let start_old = self.start;
            unsafe {
                // SAFETY: Checked above that `n < end - start`, which implies `start + n < end`.
                self.start = self.start.unchecked_add(n.unchecked_add(1));
                // SAFETY: All invariants are upheld by construction.
                Some(ElementRwLock::new(start_old, self.allocation, self.allocator.clone()))
            }
        } else {
            self.start = self.end;
            None
        }
    }
}

impl<T, A: Allocator + Clone> DoubleEndedIterator for Iter<T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);

        if self.start < self.end {
            unsafe {
                // SAFETY: Checked above that `start < end`.
                self.end = self.end.unchecked_sub(1);
                // SAFETY: All invariants are upheld by construction.
                Some(ElementRwLock::new(self.end, self.allocation, self.allocator.clone()))
            }
        } else {
            inner::cold_path();
            None
        }
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for Iter<T, A> {
    #[inline]
    fn len(&self) -> usize {
        debug_assert!(self.start <= self.end);

        // SAFETY: By construction, `start <= end`.
        unsafe { self.end.unchecked_sub(self.start) }
    }
}

impl<T, A: Allocator + Clone> FusedIterator for Iter<T, A> {}

impl<T, A: Allocator> Debug for Iter<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Iter")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("allocation", &self.allocation)
            .finish_non_exhaustive()
    }
}
