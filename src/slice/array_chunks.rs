use crate::{
    array::lock::ArrayRwLock,
    inner::{self, Allocation},
    slice::lock::SliceRwLock,
};
use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug},
    iter::FusedIterator,
    mem::ManuallyDrop,
    ops::Drop,
    ptr::NonNull,
};

/// An iterator over a `SliceRwlock` in locks to (non-overlapping) arrays of size `N`,
/// starting at the beginning of the slice.
///
/// When the slice len is not evenly divided by the array size, the last
/// up to `N-1` elements will be omitted but can be retrieved from
/// the [`remainder`] function from the iterator.
///
/// This struct is created by the [`array_chunks`] method on [`SliceRwLock`].
///
/// [`remainder`]: ArrayChunks::remainder
/// [`array_chunks`]: SliceRwLock::array_chunks
#[clippy::has_significant_drop]
pub struct ArrayChunks<T, const N: usize, A: Allocator = Global> {
    remainder_start: usize,
    remainder_len: usize,
    start: usize,
    end: usize,
    allocation: NonNull<Allocation<T>>,
    allocator: A,
}

impl<T, const N: usize, A: Allocator> ArrayChunks<T, N, A> {
    /// Creates a new instance of `ArrayChunks` without checking whether `start + len` overflows
    /// nor that `N` is non-zero.
    /// Does not increment the atomic counter.
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
        // Shenanigans to bypass the `%` operator not being const.
        // SAFETY: User-upheld invariant.
        let remainder_len = unsafe { len.checked_rem(N).unwrap_unchecked() };
        // SAFETY: `start <= start + len - len % N < start + len`.
        // Assuming user-upheld invariant, this cannot overflow.
        let end = unsafe { start.unchecked_add(len).unchecked_sub(remainder_len) };
        Self {
            remainder_start: end,
            remainder_len,
            start,
            end,
            allocation,
            allocator,
        }
    }

    /// Returns the a lock to the remainder of the original guarded slice that is not going to be
    /// returned by the iterator. The slice guarded by the returned lock has at most `N-1`
    /// elements.
    #[inline]
    pub fn remainder(self) -> SliceRwLock<T, A> {
        let orig = ManuallyDrop::new(self);
        unsafe {
            // SAFETY: All invariants are upheld by construction.
            SliceRwLock::new_not_incremented(
                orig.remainder_start,
                orig.remainder_len,
                orig.allocation,
                // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                (&raw const orig.allocator).read(),
            )
        }
    }
}

impl<T, const N: usize, A: Allocator> Drop for ArrayChunks<T, N, A> {
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

impl<T, const N: usize, A: Allocator + Clone> Iterator for ArrayChunks<T, N, A> {
    type Item = ArrayRwLock<T, N, A>;

    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);
        debug_assert!(N != 0);
        debug_assert!((self.end - self.start).is_multiple_of(N));

        if self.start < self.end {
            let start = self.start;
            unsafe {
                // SAFETY: By construction, `end - start` is a multiple of `N`.
                // Checked above that `start < end`, so they must be at least `chunk_size` apart.
                self.start = self.start.unchecked_add(N);
                // SAFETY: All invariants are upheld by construction.
                Some(ArrayRwLock::new(start, self.allocation, self.allocator.clone()))
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
        debug_assert!(self.start <= self.end);
        debug_assert!(N != 0);
        debug_assert!((self.end - self.start).is_multiple_of(N));

        // SAFETY: By construction, `start < end`.
        let len = unsafe { self.end.unchecked_sub(self.start) };
        match N.checked_mul(n) {
            Some(skip) if skip < len => unsafe {
                // SAFETY: Checked above that `skip < end - start`, which implies `start + skip < end`
                let start = self.start.unchecked_add(skip);
                // SAFETY: Checked above that `n * N < end - start`. This implies
                // `start + n * N < end`. By construction, `end - start` is a multiple
                // of `N`, so `start + n * N` and `end` must be at least `N` apart.
                self.start = start.unchecked_add(N);
                // SAFETY: All invariants are upheld by construction.
                Some(ArrayRwLock::new(start, self.allocation, self.allocator.clone()))
            },
            Some(_) => {
                self.start = self.end;
                None
            }
            _ => {
                inner::cold_path();
                None
            }
        }
    }
}

impl<T, const N: usize, A: Allocator + Clone> DoubleEndedIterator for ArrayChunks<T, N, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        debug_assert!(self.start <= self.end);
        debug_assert!(N != 0);
        debug_assert!((self.end - self.start).is_multiple_of(N));

        if self.start < self.end {
            unsafe {
                // SAFETY: By construction, `end - start` is a multiple of `N`.
                // Checked above that `start < end`, so they must be at least `chunk_size` apart.
                self.end = self.end.unchecked_sub(N);
                // SAFETY: All invariants are upheld by construction.
                Some(ArrayRwLock::new(self.end, self.allocation, self.allocator.clone()))
            }
        } else {
            inner::cold_path();
            None
        }
    }
}

impl<T, const N: usize, A: Allocator + Clone> ExactSizeIterator for ArrayChunks<T, N, A> {
    fn len(&self) -> usize {
        debug_assert!(self.start <= self.end);
        debug_assert!(N != 0);

        // SAFETY: By construction, `start < end`.
        unsafe { self.end.unchecked_sub(self.start) / N }
    }
}

impl<T, const N: usize, A: Allocator + Clone> FusedIterator for ArrayChunks<T, N, A> {}

impl<T, const N: usize, A: Allocator> Debug for ArrayChunks<T, N, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ArrayChunks")
            .field("remainder_start", &self.remainder_start)
            .field("remainder_len", &self.remainder_len)
            .field("start", &self.start)
            .field("end", &self.end)
            .field("allocation", &self.allocation)
            .finish_non_exhaustive()
    }
}
