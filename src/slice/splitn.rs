use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    iter::FusedIterator,
    ops::Drop,
    ptr::NonNull,
};

use super::{lock::SliceRwLock, panic_guard::PanicWriteGuard};
use crate::inner::{self, Allocation};

/// An iterator over a `SliceRwLock` in locks to subslices separated by elements that match a predicate
/// function, limited to a given number of splits.
///
/// This struct is created by the [`splitn`] method on [`SliceRwLock`].
///
/// [`splitn`]: SliceRwLock::splitn
#[clippy::has_significant_drop]
pub struct SplitN<T, P, A = Global>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    remaining_iters: usize,
    predicate: P,
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, P, A> SplitN<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    /// Creates a new instance of `SplitN` without checking whether `start + len` overflows.
    /// Does not increment the reference counter.
    ///
    /// # Safety
    /// See [`SliceRwLock::new`]
    #[inline]
    pub(crate) unsafe fn new_unchecked_not_increment(
        remaining_iters: usize,
        predicate: P,
        start: usize,
        len: usize,
        allocation: NonNull<Allocation<T>>,
        allocator: A,
    ) -> Self {
        debug_assert!(start.checked_add(len).is_some());

        Self {
            remaining_iters,
            predicate,
            start,
            // SAFETY: User-upheld invariant.
            end: unsafe { start.unchecked_add(len) },
            allocation,
            allocator,
        }
    }
}

impl<T, P, A> Drop for SplitN<T, P, A>
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

impl<T, P, A> Iterator for SplitN<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator + Clone,
{
    type Item = SliceRwLock<T, A>;

    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);

        match self.remaining_iters {
            0 => {
                inner::cold_path();
                None
            }
            1 => {
                inner::cold_path();
                let start_old = self.start;
                self.start = self.end;
                self.remaining_iters = 0;
                unsafe {
                    // SAFETY: All invariants are upheld by construction.
                    Some(SliceRwLock::new(
                        start_old,
                        // SAFETY: By construction, `start <= end`.
                        self.end.unchecked_sub(start_old),
                        self.allocation,
                        self.allocator.clone(),
                    ))
                }
            }
            _ => {
                let start_old = self.start;
                let guard = unsafe {
                    // SAFETY: The guard is dropped after the loop.
                    PanicWriteGuard::new(
                        // SAFETY: By construction, `allocation` points to live and valid data.
                        &Allocation::get_metadata_disjoint(self.allocation).lock,
                    )
                };
                let (streak_end, remaining_iters) = loop {
                    if inner::unlikely(self.start == self.end) {
                        break (self.end, 0);
                    }
                    // SAFETY: Checked above that `start != end`, which implies `start < end`.
                    let start_new = unsafe { self.start.unchecked_add(1) };
                    // SAFETY: By construction, `allocation` points to live and valid data
                    // and the accessed (sub)slice is locked behind local exclusive access.
                    if (self.predicate)(unsafe { Allocation::get_elem_disjoint(self.allocation, self.start) }) {
                        let tmp = self.start;
                        self.start = start_new;
                        // SAFETY: This branch guarantees that `remaining_iters > 1`.
                        break (tmp, unsafe { self.remaining_iters.unchecked_sub(1) });
                    } else {
                        self.start = start_new;
                    }
                };
                drop(guard);
                self.remaining_iters = remaining_iters;
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
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        debug_assert!(self.start <= self.end);

        if self.remaining_iters == 0 {
            (0, Some(0))
        } else {
            // In the extreme case, every element matches the predicate.
            // SAFETY: By construction, `start <= end`.
            (
                1,
                Some(usize::min(
                    self.remaining_iters,
                    unsafe { self.end.unchecked_sub(self.start) } + 1,
                )),
            )
        }
    }
}

impl<T, P, A> FusedIterator for SplitN<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator + Clone,
{
}

impl<T, P, A: Allocator> Debug for SplitN<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SplitN")
            .field("remaining_iters", &self.remaining_iters)
            .field("start", &self.start)
            .field("end", &self.end)
            .field("allocation", &self.allocation)
            .finish_non_exhaustive()
    }
}
