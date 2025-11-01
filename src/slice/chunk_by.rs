use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    iter::FusedIterator,
    ops::Drop,
    ptr::NonNull,
};

use super::{lock::SliceRwLock, panic_guard::PanicWriteGuard};
use crate::inner::{self, Allocation};

/// An iterator over a `SliceRwLock` in locks to (non-overlapping) chunks separated by a predicate.
///
/// This struct is created by the [`chunk_by`] method on [`SliceRwLock`].
///
/// [`chunk_by`]: SliceRwLock::chunk_by
#[clippy::has_significant_drop]
pub struct ChunkBy<T, P, A = Global>
where
    P: FnMut(&T, &T) -> bool,
    A: Allocator,
{
    predicate: P,
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, P, A> ChunkBy<T, P, A>
where
    P: FnMut(&T, &T) -> bool,
    A: Allocator,
{
    /// Creates a new instance of `ChunkBy` without checking whether `start + len` overflows.
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
}

impl<T, P, A> Drop for ChunkBy<T, P, A>
where
    P: FnMut(&T, &T) -> bool,
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

impl<T, P, A> Iterator for ChunkBy<T, P, A>
where
    P: FnMut(&T, &T) -> bool,
    A: Allocator + Clone,
{
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let start_old = self.start;
            let guard = unsafe {
                // SAFETY: The guard is dropped after the loop.
                PanicWriteGuard::new(
                    // By construction, `allocation` points to live and valid data.
                    &Allocation::get_metadata_disjoint(self.allocation).lock,
                )
            };
            // SAFETY: Checked above that `start < end`.
            while self.start < unsafe { self.end.unchecked_sub(1) } {
                // SAFETY: Checked above that `start < end - 1`.
                let start_new = unsafe { self.start.unchecked_add(1) };
                // SAFETY: By construction, `allocation` points to live and valid data
                // and the accessed (sub)slice is locked behind local exclusive access.
                if unsafe {
                    (self.predicate)(
                        Allocation::get_elem_disjoint(self.allocation, self.start),
                        Allocation::get_elem_disjoint(self.allocation, start_new),
                    )
                } {
                    self.start = start_new
                } else {
                    break;
                }
            }
            drop(guard);
            unsafe {
                // SAFETY: The loop guarantees that `start <= end - 1`.
                self.start = self.start.unchecked_add(1);
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(
                    start_old,
                    // SAFETY: By construction, `start_old < start`.
                    self.start.unchecked_sub(start_old),
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
        if len == 0 { (0, Some(0)) } else { (1, Some(len)) }
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<T, P, A> DoubleEndedIterator for ChunkBy<T, P, A>
where
    P: FnMut(&T, &T) -> bool,
    A: Allocator + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);

        if self.start < self.end {
            let end_old = self.end;
            let guard = unsafe {
                // SAFETY: The guard is dropped after the loop.
                PanicWriteGuard::new(
                    // By construction, `allocation` points to live and valid data.
                    &Allocation::get_metadata_disjoint(self.allocation).lock,
                )
            };
            // SAFETY: Checked above that `start < end`.
            self.end = unsafe { self.end.unchecked_sub(1) };
            // SAFETY: Checked above that `start < end`.
            while unsafe { self.start.unchecked_add(1) } < self.end {
                // SAFETY: Checked above that `start + 1 < end`.
                let end_new = unsafe { self.end.unchecked_sub(1) };
                // SAFETY: By construction, `allocation` points to live and valid data
                // and the accessed (sub)slice is locked behind local exclusive access.
                if unsafe {
                    (self.predicate)(
                        Allocation::get_elem_disjoint(self.allocation, end_new),
                        Allocation::get_elem_disjoint(self.allocation, self.end),
                    )
                } {
                    self.end = end_new;
                } else {
                    break;
                }
            }
            drop(guard);
            unsafe {
                // SAFETY: All invariants are upheld by construction.
                Some(SliceRwLock::new(
                    self.end,
                    // By construction, `end < end_old`.
                    end_old.unchecked_sub(self.end),
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

impl<T, P, A> FusedIterator for ChunkBy<T, P, A>
where
    P: FnMut(&T, &T) -> bool,
    A: Allocator + Clone,
{
}

impl<T, P, A: Allocator> Debug for ChunkBy<T, P, A>
where
    P: FnMut(&T, &T) -> bool,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Chunks")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("allocation", &self.allocation)
            .finish_non_exhaustive()
    }
}
