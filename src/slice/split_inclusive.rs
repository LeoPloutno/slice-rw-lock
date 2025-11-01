#[allow(unused_imports)]
use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    iter::FusedIterator,
    mem::ManuallyDrop,
    ops::Drop,
    ptr::NonNull,
};

use super::{lock::SliceRwLock, panic_guard::PanicWriteGuard};
use crate::inner::{self, Allocation};

/// An iterator over a `SliceRwLock` in locks to subslices separated by elements that match a predicate
/// function. Unlike `Split`, it contains the matched part as a terminator
/// of the subslice.
///
/// This struct is created by the [`split_inclusive`] method on [`SliceRwLock`].
///
/// [`split_inclusive`]: SliceRwLock::split_inclusive
#[clippy::has_significant_drop]
pub struct SplitInclusive<T, P, A = Global>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    predicate: P,
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, P, A> SplitInclusive<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    /// Creates a new instance of `SplitInclusive` without checking whether `start + len` overflows.
    /// Does not increment the reference counter.
    ///
    /// # Safety
    /// See [`SliceRwLock::new`]
    #[inline]
    pub(crate) unsafe fn new_unchecked_not_increment(
        predicate: P,
        start: usize,
        len: usize,
        allocation: NonNull<Allocation<T>>,
        allocator: A,
    ) -> Self {
        debug_assert!(start.checked_add(len).is_some());

        Self {
            predicate,
            start,
            // SAFETY: User-upheld invariant.
            end: unsafe { start.unchecked_add(len) },
            allocation,
            allocator,
        }
    }

    /// Returns a lock to a slice which contains items not yet handled by split.
    #[cfg(feature = "split_as_slice")]
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

impl<T, P, A> Drop for SplitInclusive<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
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

impl<T, P, A> Iterator for SplitInclusive<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator + Clone,
{
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let start_old = self.start;
            let guard = unsafe {
                // SAFETY: The guard is dropped after the loop.
                PanicWriteGuard::new(
                    // SAFETY: By construction, `allocation` points to live and valid data.
                    &Allocation::get_metadata_disjoint(self.allocation).lock,
                )
            };
            let streak_end = loop {
                if inner::unlikely(self.start == self.end) {
                    break self.end;
                }
                // SAFETY: By construction, `allocation` points to live and valid data
                // and the accessed (sub)slice is locked behind local exclusive access.
                // Checked above that `start < end`.
                let matches_pred =
                    unsafe { (self.predicate)(Allocation::get_elem_disjoint(self.allocation, self.start)) };
                // SAFETY: Checked above that `start < end`.
                self.start = unsafe { self.start.unchecked_add(1) };
                if matches_pred {
                    break self.start;
                }
            };
            drop(guard);
            unsafe {
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(
                    start_old,
                    // SAFETY: By construction, `start_old <= start <= streak_end`.
                    streak_end.unchecked_sub(start_old),
                    self.allocation,
                    self.allocator.clone(),
                ))
            }
        } else {
            inner::cold_path();
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        debug_assert!(self.start <= self.end);

        // SAFETY: By construction, `start <= end`.
        let len = unsafe { self.end.unchecked_sub(self.start) };
        if len == 0 {
            (0, Some(0))
        } else {
            // In the extreme case, every element matches the predicate.
            (1, Some(len))
        }
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<T, P, A> DoubleEndedIterator for SplitInclusive<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let end_old = self.end;
            let guard = unsafe {
                // SAFETY: The guard is dropped after the loop.
                PanicWriteGuard::new(
                    // SAFETY: By construction, `allocation` points to live and valid data.
                    &Allocation::get_metadata_disjoint(self.allocation).lock,
                )
            };
            // Even if the very last element matches the predicate,
            // it will still be included in this iteration as the terminator.
            // SAFETY: Checked above that `start < end`.
            self.end = unsafe { self.end.unchecked_sub(1) };
            let streak_start = loop {
                if inner::unlikely(self.start == self.end) {
                    break self.start;
                }
                // SAFETY: Checked above that `start != end`, which implies `start < end`.
                let end_new = unsafe { self.end.unchecked_sub(1) };
                // SAFETY: By construction, `allocation` points to live and valid data
                // and the accessed (sub)slice is locked behind local exclusive access.
                if (self.predicate)(unsafe { Allocation::get_elem_disjoint(self.allocation, end_new) }) {
                    break self.end;
                } else {
                    self.end = end_new;
                }
            };
            drop(guard);
            unsafe {
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(
                    streak_start,
                    // SAFETY: By construction, `streak_start <= end <= end_old`.
                    end_old.unchecked_sub(streak_start),
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

impl<T, P, A> FusedIterator for SplitInclusive<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator + Clone,
{
}

impl<T, P, A: Allocator> Debug for SplitInclusive<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitInclusive")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("allocation", &self.allocation)
            .finish_non_exhaustive()
    }
}
