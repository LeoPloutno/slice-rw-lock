use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    iter::FusedIterator,
    ops::Drop,
    ptr::NonNull,
};

use super::{lock::SliceRwLock, panic_guard::PanicWriteGuard};
use crate::inner::{self, alloc::Allocation};

/// An iterator over a `SliceRwLock` in locks to subslices separated by elements that match a predicate
/// function, limited to a given number of splits, starting from the end of the slice.
///
/// This struct is created by the [`rsplitn`] method on [`SliceRwLock`].
///
/// [`rsplitn`]: SliceRwLock::rsplitn
#[clippy::has_significant_drop]
pub struct RSplitN<T, P, A = Global>
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

impl<T, P, A> RSplitN<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    /// Creates a new instance of `RSplitN` without checking whether `start + len` overflows.
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

impl<T, P, A> Drop for RSplitN<T, P, A>
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

impl<T, P, A> Iterator for RSplitN<T, P, A>
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
            },
            1 => {
                inner::cold_path();
                let end_old = self.end;
                self.end = self.start;
                self.remaining_iters = 0;
                unsafe {
                    // SAFETY: All invariants are upheld by construction.
                    Some(SliceRwLock::new(
                        self.start,
                        // SAFETY: By construction, `start <= end`.
                        end_old.unchecked_sub(self.start),
                        self.allocation,
                        self.allocator.clone()
                    ))
                }
            },
            _ => {
                let end_old = self.end;
                let guard = unsafe {
                    // SAFETY: The guard is dropped after the loop.
                    PanicWriteGuard::new(
                        // By construction, `allocation` points to live and valid data.
                        &Allocation::get_metadata_disjoint(self.allocation).lock,
                    )
                };
                let (streak_start, remainig_iters) = loop {
                    if inner::unlikely(self.start == self.end) {
                        break (self.start, 0);
                    }
                    // SAFETY: Checked above that `start != end`, which implies `start < end`.
                    let end_new = unsafe { self.end.unchecked_sub(1) };
                    // SAFETY: By construction, `allocation` points to live and valid data
                    // and the accessed (sub)slice is locked behind local exclusive access.
                    if (self.predicate)(unsafe { Allocation::get_elem_disjoint(self.allocation, end_new) }) {
                        // SAFETY: This branch guarantees that `remaining_iters > 1`.
                        break (self.end, unsafe { self.remaining_iters.unchecked_sub(1) });
                    } else {
                        self.end = end_new;
                    }
                };
                drop(guard);
                self.remaining_iters = remainig_iters;
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
            (1, Some(usize::min(self.remaining_iters, unsafe { self.end.unchecked_sub(self.start) } + 1)))
        }
    }
}


impl<T, P, A> FusedIterator for RSplitN<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator + Clone,
{
}

impl<T, P, A: Allocator> Debug for RSplitN<T, P, A>
where
    P: FnMut(&T) -> bool,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RSplitN")
            .field("remaining_iters", &self.remaining_iters)
            .field("start", &self.start)
            .field("end", &self.end)
            .field("allocation", &self.allocation)
            .finish_non_exhaustive()
    }
}
