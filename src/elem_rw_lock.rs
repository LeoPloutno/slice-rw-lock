pub(crate) mod iter {
    use super::lock::RwLock;
    use crate::inner::{Allocation, LockState};
    use std::{
        iter::FusedIterator,
        mem::MaybeUninit,
        process,
        ptr::NonNull,
        sync::atomic::{self, Ordering},
    };
    pub struct Iter<T> {
        allocation: NonNull<Allocation<T>>,
        start: usize,
        end: usize,
    }

    impl<T> Iter<T> {
        pub fn new_uninit(len: usize) -> Iter<MaybeUninit<T>> {
            Iter {
                allocation: unsafe { Allocation::alloc_uninit(len) },
                start: 0,
                end: len,
            }
        }

        pub fn new_zeroed(len: usize) -> Iter<MaybeUninit<T>> {
            Iter {
                allocation: unsafe { Allocation::alloc_zeroed(len) },
                start: 0,
                end: len,
            }
        }
        
        pub fn from_vec(v: Vec<T>) -> Self {
            let old_ptr = Box::into_raw(v.into_boxed_slice());
            Iter {
                allocation: unsafe { Allocation::realloc(NonNull::new_unchecked(old_ptr)) },
                start: 0,
                end: old_ptr.len()
            }
        }
    }

    impl<T> Iterator for Iter<T> {
        type Item = RwLock<T>;

        fn next(&mut self) -> Option<Self::Item> {
            if self.start == self.end {
                None
            } else {
                let ret = Some(Self::Item {
                    allocation: self.allocation,
                    idx: self.start,
                });
                self.start += 1;

                if unsafe {
                    Allocation::get_metadata_disjoint(self.allocation)
                        .state
                        .fetch_increment_counter_unchecked(Ordering::Relaxed)
                } == LockState::MAX_COUNT
                {
                    process::abort();
                }
                ret
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.len();
            (len, Some(len))
        }

        #[inline]
        fn count(self) -> usize {
            self.len()
        }

        #[inline]
        fn last(mut self) -> Option<Self::Item> {
            self.next_back()
        }

        #[inline]
        fn nth(&mut self, n: usize) -> Option<Self::Item> {
            self.start = Ord::min(self.start + n, self.end);
            self.next()
        }
    }

    impl<T> DoubleEndedIterator for Iter<T> {
        fn next_back(&mut self) -> Option<Self::Item> {
            if self.start == self.end {
                None
            } else {
                self.end -= 1;
                if unsafe {
                    Allocation::get_metadata_disjoint(self.allocation)
                        .state
                        .fetch_increment_counter_unchecked(Ordering::Relaxed)
                } == LockState::MAX_COUNT
                {
                    process::abort();
                }
                Some(Self::Item {
                    allocation: self.allocation,
                    idx: self.end,
                })
            }
        }
    }

    impl<T> ExactSizeIterator for Iter<T> {
        #[inline]
        fn len(&self) -> usize {
            self.end - self.start
        }
    }

    impl<T> FusedIterator for Iter<T> {}

    impl<T> Drop for Iter<T> {
        fn drop(&mut self) {
            if unsafe {
                Allocation::get_metadata_disjoint(self.allocation)
                    .state
                    .fetch_decrement_counter_unchecked(Ordering::Release)
            } == 1
            {
                atomic::fence(Ordering::Acquire);
                unsafe {
                    Allocation::dealloc(self.allocation);
                }
            }
        }
    }
}

pub(crate) mod lock {
    use super::{read_slice::RwLockReadSliceGuard, write::RwLockWriteGuard, write_slice::RwLockWriteSliceGuard};
    use crate::inner::Allocation;
    use std::{
        mem::{self, MaybeUninit},
        ptr::NonNull,
        sync::{
            LockResult, PoisonError, TryLockError, TryLockResult,
            atomic::{self, Ordering},
        },
    };

    pub struct RwLock<T> {
        pub(super) allocation: NonNull<Allocation<T>>,
        pub(super) idx: usize,
    }

    impl<T> RwLock<T> {
        pub fn write(&mut self) -> LockResult<RwLockWriteGuard<'_, T>> {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
            metadata.lock.write();
            let guard = RwLockWriteGuard(self);
            if metadata.state.is_poisoned() {
                LockResult::Err(PoisonError::new(guard))
            } else {
                LockResult::Ok(guard)
            }
        }

        pub fn try_write(&mut self) -> TryLockResult<RwLockWriteGuard<'_, T>> {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
            if metadata.lock.try_write() {
                let guard = RwLockWriteGuard(self);
                if metadata.state.is_poisoned() {
                    TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
                } else {
                    TryLockResult::Ok(guard)
                }
            } else {
                TryLockResult::Err(TryLockError::WouldBlock)
            }
        }

        pub fn read_slice(&self) -> LockResult<RwLockReadSliceGuard<'_, T>> {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
            metadata.lock.read_slice();
            let guard = RwLockReadSliceGuard(self);
            if metadata.state.is_poisoned() {
                LockResult::Err(PoisonError::new(guard))
            } else {
                LockResult::Ok(guard)
            }
        }

        pub fn try_read_slice(&self) -> TryLockResult<RwLockReadSliceGuard<'_, T>> {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
            if metadata.lock.try_read_slice() {
                let guard = RwLockReadSliceGuard(self);
                if metadata.state.is_poisoned() {
                    TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
                } else {
                    TryLockResult::Ok(guard)
                }
            } else {
                TryLockResult::Err(TryLockError::WouldBlock)
            }
        }

        pub fn write_slice(&mut self) -> LockResult<RwLockWriteSliceGuard<'_, T>> {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
            metadata.lock.write_slice();
            let guard = RwLockWriteSliceGuard(self);
            if metadata.state.is_poisoned() {
                LockResult::Err(PoisonError::new(guard))
            } else {
                LockResult::Ok(guard)
            }
        }

        pub fn try_write_slice(&mut self) -> TryLockResult<RwLockWriteSliceGuard<'_, T>> {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.allocation) };
            if metadata.lock.try_write_slice() {
                let guard = RwLockWriteSliceGuard(self);
                if metadata.state.is_poisoned() {
                    TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
                } else {
                    TryLockResult::Ok(guard)
                }
            } else {
                TryLockResult::Err(TryLockError::WouldBlock)
            }
        }

        #[inline]
        pub fn is_poisoned(&self) -> bool {
            unsafe { Allocation::get_metadata_disjoint(self.allocation) }
                .state
                .is_poisoned()
        }

        #[inline]
        pub fn clear_poison(&self) {
            unsafe { Allocation::get_metadata_disjoint(self.allocation) }
                .state
                .clear_poison();
        }
    }

    impl<T> RwLock<MaybeUninit<T>> {
        pub const unsafe fn assume_init(self) -> RwLock<T> {
            let (ptr, len) = self.allocation.to_raw_parts();
            let idx = self.idx;
            mem::forget(self);
            RwLock::<T> {
                allocation: NonNull::from_raw_parts(ptr, len),
                idx,
            }
        }
    }

    unsafe impl<T: Send + Sync> Send for RwLock<T> {}

    impl<T> Drop for RwLock<T> {
        fn drop(&mut self) {
            if unsafe {
                Allocation::get_metadata_disjoint(self.allocation)
                    .state
                    .fetch_decrement_counter_unchecked(Ordering::Release)
            } == 1
            {
                atomic::fence(Ordering::Acquire);
                unsafe {
                    Allocation::dealloc(self.allocation);
                }
            }
        }
    }
}

pub(crate) mod read_slice {
    use super::lock::RwLock;
    use crate::inner::Allocation;
    use std::{ops::Deref, thread};

    pub struct RwLockReadSliceGuard<'a, T>(pub(super) &'a RwLock<T>);

    impl<'a, T> Deref for RwLockReadSliceGuard<'a, T> {
        type Target = [T];

        fn deref(&self) -> &Self::Target {
            unsafe { &self.0.allocation.as_ref().slice }
        }
    }

    impl<'a, T> Drop for RwLockReadSliceGuard<'a, T> {
        fn drop(&mut self) {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
            if thread::panicking() {
                metadata.state.poison();
            }
            unsafe {
                metadata.lock.drop_slice_reader_unchecked();
            }
        }
    }
}

pub(crate) mod write {
    use super::lock::RwLock;
    use crate::inner::Allocation;
    use std::{
        ops::{Deref, DerefMut},
        thread,
    };

    pub struct RwLockWriteGuard<'a, T>(pub(super) &'a mut RwLock<T>);

    impl<'a, T> Deref for RwLockWriteGuard<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            &*unsafe { Allocation::get_elem_mut_disjoint(self.0.allocation, self.0.idx) }
        }
    }

    impl<'a, T> DerefMut for RwLockWriteGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { Allocation::get_elem_mut_disjoint(self.0.allocation, self.0.idx) }
        }
    }

    impl<'a, T> Drop for RwLockWriteGuard<'a, T> {
        fn drop(&mut self) {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
            if thread::panicking() {
                metadata.state.poison();
            }
            unsafe {
                metadata.lock.drop_writer_unchecked();
            }
        }
    }
}

pub(crate) mod write_slice {
    use super::lock::RwLock;
    use crate::inner::Allocation;
    use std::{
        ops::{Deref, DerefMut},
        thread,
    };

    pub struct RwLockWriteSliceGuard<'a, T>(pub(super) &'a mut RwLock<T>);

    impl<'a, T> Deref for RwLockWriteSliceGuard<'a, T> {
        type Target = [T];

        fn deref(&self) -> &Self::Target {
            &*unsafe { Allocation::get_slice_mut_disjoint(self.0.allocation) }
        }
    }

    impl<'a, T> DerefMut for RwLockWriteSliceGuard<'a, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { Allocation::get_slice_mut_disjoint(self.0.allocation) }
        }
    }

    impl<'a, T> Drop for RwLockWriteSliceGuard<'a, T> {
        fn drop(&mut self) {
            let metadata = unsafe { Allocation::get_metadata_disjoint(self.0.allocation) };
            if thread::panicking() {
                metadata.state.poison();
            }
            unsafe {
                metadata.lock.drop_slice_writer_unchecked();
            }
        }
    }
}
