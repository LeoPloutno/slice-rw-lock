use super::{read_all::ElemRwLockReadAllGuard, write::ElemRwLockWriteGuard, write_all::ElemRwLockWriteAllGuard};
use crate::{
    inner::{Allocation, State},
    slice::lock::SliceRwLock,
};
use std::{
    alloc::{Allocator, Global},
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    panic::{RefUnwindSafe, UnwindSafe},
    process,
    ptr::NonNull,
    sync::{LockResult, PoisonError, TryLockError, TryLockResult, atomic::Ordering},
};

pub(super) struct InnerElemRwLock<T> {
    pub(super) idx: usize,
    pub(super) allocation: NonNull<Allocation<T>>,
}

/// A reader-writer lock guarding an element of a slice.
///
/// This lock gives exclusive subfield write access to a single element of the underlying slice.
/// It can also give global read and write accesses to the slice.
///
/// # Examples
///
/// Mutate an element in a single-threaded environment:
/// ```
/// # use slice_rw_lock::SliceRwLock;
/// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
/// let (mut first_elem, slice) = slice.split_first().unwrap();
///
/// let mut guard = first_elem.write().unwrap();
/// *guard = 12;
/// drop(guard);
///
/// assert_eq!(&*slice.read_all().unwrap(), &[12, 1, 2]);
/// ```
///
/// Mutate two elements in parallel without blocking:
/// ```
/// # use slice_rw_lock::SliceRwLock;
/// # use std::thread;
/// let slice = SliceRwLock::from_vec(vec![0, 1]);
/// let (mut first_elem, slice) = slice.split_first().unwrap();
/// let (mut second_elem, slice) = slice.split_first().unwrap();
///
/// let handle = thread::spawn(move || {
///     // No global access is acquired elsewhere - cannot fail.
///     let not_blocked = first_elem.try_write();
///     assert!(not_blocked.is_ok());
///     *not_blocked.unwrap() = 24;
/// });
///
/// let mut guard = second_elem.write().unwrap();
/// *guard = 12;
///
/// handle.join().unwrap();
/// drop(guard);
///
/// assert_eq!(&*slice.read_all().unwrap(), &[12, 24]);
/// ```
#[clippy::has_significant_drop]
pub struct ElemRwLock<T, A: Allocator = Global> {
    pub(super) inner: InnerElemRwLock<T>,
    allocator: A,
}

impl<T, A: Allocator> ElemRwLock<T, A> {
    /// Creates a new lock to the underlying `allocation` without incrementing the reference counter.
    ///
    /// # Safety
    ///
    /// * `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// * `idx` must index an element inside the array pointed to by `allocation`.
    /// * The reference counter must not be zero when this function is called.
    #[inline]
    pub(crate) unsafe fn new_not_incremented(idx: usize, allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        Self {
            allocator,
            inner: InnerElemRwLock { idx, allocation },
        }
    }

    /// Creates a new lock to the underlying `allocation`. Atomically increments the reference counter.
    ///
    /// # Safety
    ///
    /// * `allocation` must point to a live and valid instance of `Allocation<T>`.
    /// * `idx` must index an element inside the array pointed to by `allocation`.
    pub(crate) unsafe fn new(idx: usize, allocation: NonNull<Allocation<T>>, allocator: A) -> Self {
        if unsafe {
            Allocation::get_metadata_disjoint(allocation)
                .state
                .fetch_increment_counter_unchecked(Ordering::Release)
        } == State::MAX_COUNT
        {
            process::abort();
        }
        // SAFETY: User-upheld invariants.
        unsafe { Self::new_not_incremented(idx, allocation, allocator) }
    }

    /// Returns a lock to the entire slice wrapped in `Ok` if `self` is the only
    /// entity guarding the slice. Otherwise, returns `Err` containing the original lock.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    ///
    /// let (first_elem, slice) = slice.split_first().unwrap();
    /// let not_all = first_elem.into_all();
    /// assert!(not_all.is_err());
    ///
    /// let lock = not_all.unwrap_err();
    /// drop(slice);
    /// assert!(lock.into_all().is_ok());
    /// ```
    pub fn into_all(self) -> Result<SliceRwLock<T, A>, Self> {
        // SAFETY: By construction, `allocation` points to live amd valid data.
        if unsafe {
            Allocation::get_metadata_disjoint(self.inner.allocation)
                .state
                .get_counter()
        } == 1
        {
            let orig = ManuallyDrop::new(self);
            Ok(unsafe {
                // SAFETY: All invariants are upheld by construction.
                SliceRwLock::new_not_incremented(
                    0,
                    // SAFETY: By construction, `allocation` points to live amd valid data.
                    Allocation::len(orig.inner.allocation),
                    orig.inner.allocation,
                    // SAFETY: The allocator is not accessed after this line and is forgotten at the end of this function.
                    (&raw const orig.allocator).read(),
                )
            })
        } else {
            Err(self)
        }
    }

    /// Locks the allocation guarded by this 'ElemRwLock' with shared global read access, blocking
    /// the current thread until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more subfield nor global writers which
    /// hold the locks to the guarded allocation. There may be other readers currently when
    /// this method returns. This method does not provide any guarantees with
    /// respect to the ordering of whether contentious readers or writers will
    /// acquire the lock first.
    ///
    /// Returns an RAII guard which will release this thread's shared access
    /// once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElemRwLock` is poisoned. An
    /// `ElemRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired. The acquired lock guard will be contained in the returned
    /// error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::{sync::Barrier, thread};
    /// let barrier = Barrier::new(2);
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    /// let (first_elem, mut slice) = slice.split_first().unwrap();
    ///
    /// thread::scope(|s| {
    ///     let handle = s.spawn(|| {
    ///         let mut guard = slice.write().unwrap();
    ///         barrier.wait();
    ///         guard[0] = 12;
    ///         drop(guard);
    ///         // Checked that the lock is not poisoned in the main thread.
    ///         barrier.wait();
    ///         let guard = slice.write().unwrap();
    ///         panic!();
    ///     });
    ///
    ///     // Created `guard` in the spawned thread.
    ///     barrier.wait();
    ///     // Block until `guard` is dropped in the spawned thread.
    ///     let guard = first_elem.read_all();
    ///     assert!(guard.is_ok());
    ///     assert_eq!(&*guard.unwrap(), &[0, 12 ,2]);
    ///     barrier.wait();
    ///     // Panicked in the spawned thread.
    ///     handle.join();
    ///     assert!(first_elem.read_all().is_err());
    /// });
    /// ```
    pub fn read_all(&self) -> LockResult<ElemRwLockReadAllGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.read_all();
        let guard = ElemRwLockReadAllGuard(&self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to acquire this `ElemRwLock` with shared global read access.
    ///
    /// If the access could not be granted at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared access
    /// when it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the [`Poisoned`] error if the `ElemRwLock` is
    /// poisoned. An `ElemRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ElemRwLock` could
    /// not be acquired because it was already locked exclusively.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::{sync::{Barrier, TryLockError}, thread};
    /// let barrier = Barrier::new(2);
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    /// let (first_elem, mut slice) = slice.split_first().unwrap();
    ///
    /// thread::scope(|s| {
    ///     let handle = s.spawn(|| {
    ///         let mut guard = slice.write().unwrap();
    ///         barrier.wait();
    ///         // Checked that `read_all` would block in the main thread.
    ///         barrier.wait();
    ///         guard[0] = 12;
    ///         drop(guard);
    ///         barrier.wait();
    ///         // Checked that `read_all` would no longer block in the main thread.
    ///         barrier.wait();
    ///         let guard = slice.write().unwrap();
    ///         panic!();
    ///     });
    ///
    ///     // Created `guard` in the spawned thread.
    ///     barrier.wait();
    ///     assert!(matches!(first_elem.try_read_all(), Err(TryLockError::WouldBlock)));
    ///     barrier.wait();
    ///     // Mutated the second element and dropped `guard` in the spawned thread.
    ///     barrier.wait();
    ///     let guard = first_elem.try_read_all();
    ///     assert!(guard.is_ok());
    ///     assert_eq!(&*guard.unwrap(), &[0, 12, 2]);
    ///     barrier.wait();
    ///     // Panicked in the spawned thread.
    ///     handle.join();
    ///     assert!(matches!(first_elem.try_read_all(), Err(TryLockError::Poisoned(_))));
    /// });
    /// ```
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_read_all(&self) -> TryLockResult<ElemRwLockReadAllGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_read_all() {
            let guard = ElemRwLockReadAllGuard(&self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the element guarded by this `ElemRwLock` with exclusive subfiield write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while a global writer or any readers
    /// currently have access to the guarded allocation.
    /// It will, however, return if there are only other subfield writers currently.
    ///
    /// Returns an RAII guard which will release this thread's exclusive access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElemRwLock` is poisoned. An
    /// `ElemRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::{sync::Barrier, thread};
    /// let barrier = Barrier::new(2);
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    /// let (mut first_elem, slice) = slice.split_first().unwrap();
    /// let (mut second_elem, slice) = slice.split_first().unwrap();
    ///
    /// thread::scope(|s| {
    ///     let handle = s.spawn(|| {
    ///         *first_elem.write().unwrap() = 12;
    ///         barrier.wait();
    ///         // Checked the slice contents in the main thread.
    ///         barrier.wait();
    ///         let guard = first_elem.write().unwrap();
    ///         panic!();
    ///     });
    ///
    ///     *second_elem.write().unwrap() = 24;
    ///     // Mutated the first element in the spawned thread.
    ///     barrier.wait();
    ///     assert_eq!(&*slice.read_all().unwrap(), &[12, 24, 2]);
    ///     barrier.wait();
    ///     // Panicked in the spawned thread.
    ///     handle.join();
    ///     assert!(second_elem.write().is_err());
    /// });
    /// ```
    pub fn write(&mut self) -> LockResult<ElemRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write();
        let guard = ElemRwLockWriteGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `ElemRwLock` with exclusive subfield write access.
    ///
    /// If the lock could not be acquired at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the lock when
    /// it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the [`Poisoned`] error if the `ElemRwLock` is
    /// poisoned. An `ElemRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ElemRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::{sync::{Barrier, TryLockError}, thread};
    /// let barrier = Barrier::new(2);
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    /// let (mut first_elem, mut slice) = slice.split_first().unwrap();
    ///
    /// thread::scope(|s| {
    ///     let handle = s.spawn(|| {
    ///         let guard = slice.read_all().unwrap();
    ///         barrier.wait();
    ///         // Checked that `write` would block in the main thread.
    ///         barrier.wait();
    ///         drop(guard);
    ///         barrier.wait();
    ///         // Checked that `write` would no longer block in the main thread.
    ///         barrier.wait();
    ///         let guard = slice.write().unwrap();
    ///         panic!();
    ///     });
    ///
    ///     // Created `guard` in the spawned thread.
    ///     barrier.wait();
    ///     assert!(matches!(first_elem.try_write(), Err(TryLockError::WouldBlock)));
    ///     barrier.wait();
    ///     // Dropped `guard` in the spawned thread.
    ///     barrier.wait();
    ///     assert!(first_elem.try_write().is_ok());
    ///     barrier.wait();
    ///     // Panicked in the spawned thread.
    ///     handle.join();
    ///     assert!(matches!(first_elem.try_write(), Err(TryLockError::Poisoned(_))));
    /// });
    /// ```
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write(&mut self) -> TryLockResult<ElemRwLockWriteGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write() {
            let guard = ElemRwLockWriteGuard(&mut self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Locks the allocation guarded by this `ElemRwLock` with exclusive global write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other writers or other readers
    /// currently have access to the lock.
    ///
    /// Returns an RAII guard which will release this thread's exclusive access once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `ElemRwLock` is poisoned. An
    /// `ElemRwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired. The acquired
    /// lock guard will be contained in the returned error.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::{sync::Barrier, thread};
    /// let barrier = Barrier::new(2);
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    /// let (mut first_elem, mut slice) = slice.split_first().unwrap();
    ///
    /// thread::scope(|s| {
    ///     let handle = s.spawn(|| {
    ///         let mut guard = slice.write().unwrap();
    ///         barrier.wait();
    ///         guard[0] = 12;
    ///         drop(guard);
    ///         // Checked that the lock is not poisoned in the main thread.
    ///         barrier.wait();
    ///         let guard = slice.write().unwrap();
    ///         panic!();
    ///     });
    ///
    ///     // Created `guard` in the spawned thread.
    ///     barrier.wait();
    ///     // Block until `guard` is dropped in the spawned thread.
    ///     let guard = first_elem.write_all();
    ///     assert!(guard.is_ok());
    ///     assert_eq!(&mut *guard.unwrap(), &mut [0, 12 ,2]);
    ///     barrier.wait();
    ///     // Panicked in the spawned thread.
    ///     handle.join();
    ///     assert!(first_elem.write_all().is_err());
    /// });
    /// ```
    pub fn write_all(&mut self) -> LockResult<ElemRwLockWriteAllGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        metadata.lock.write_all();
        let guard = ElemRwLockWriteAllGuard(&mut self.inner, PhantomData);
        if metadata.state.is_poisoned() {
            LockResult::Err(PoisonError::new(guard))
        } else {
            LockResult::Ok(guard)
        }
    }

    /// Attempts to lock this `ElemRwLock` with exclusive global write access.
    ///
    /// If the lock could not be acquired at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the lock when
    /// it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the [`Poisoned`] error if the `ElemRwLock` is
    /// poisoned. An `ElemRwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired. An acquired lock guard will be contained
    /// in the returned error.
    ///
    /// This function will return the [`WouldBlock`] error if the `ElemRwLock` could
    /// not be acquired because it was already locked.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::{sync::{Barrier, TryLockError}, thread};
    /// let barrier = Barrier::new(2);
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    /// let (mut first_elem, mut slice) = slice.split_first().unwrap();
    ///
    /// thread::scope(|s| {
    ///     let handle = s.spawn(|| {
    ///         let mut guard = slice.write().unwrap();
    ///         barrier.wait();
    ///         // Checked that `write_all` would block in the main thread.
    ///         barrier.wait();
    ///         guard[0] = 12;
    ///         drop(guard);
    ///         barrier.wait();
    ///         // Checked that `write_all` would no longer block in the main thread.
    ///         barrier.wait();
    ///         let guard = slice.write().unwrap();
    ///         panic!();
    ///     });
    ///
    ///     // Created `guard` in the spawned thread.
    ///     barrier.wait();
    ///     assert!(matches!(first_elem.try_write_all(), Err(TryLockError::WouldBlock)));
    ///     barrier.wait();
    ///     // Mutated the second element and dropped `guard` in the spawned thread.
    ///     barrier.wait();
    ///     let guard = first_elem.try_write_all();
    ///     assert!(guard.is_ok());
    ///     assert_eq!(&mut *guard.unwrap(), &mut [0, 12, 2]);
    ///     barrier.wait();
    ///     // Panicked in the spawned thread.
    ///     handle.join();
    ///     assert!(matches!(first_elem.try_write_all(), Err(TryLockError::Poisoned(_))));
    /// });
    /// ```
    ///
    /// [`Poisoned`]: TryLockError::Poisoned
    /// [`WouldBlock`]: TryLockError::WouldBlock
    pub fn try_write_all(&mut self) -> TryLockResult<ElemRwLockWriteAllGuard<'_, T>> {
        // By construction, `allocation` points to live and valid data.
        let metadata = unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) };
        if metadata.lock.try_write_all() {
            let guard = ElemRwLockWriteAllGuard(&mut self.inner, PhantomData);
            if metadata.state.is_poisoned() {
                TryLockResult::Err(TryLockError::Poisoned(PoisonError::new(guard)))
            } else {
                TryLockResult::Ok(guard)
            }
        } else {
            TryLockResult::Err(TryLockError::WouldBlock)
        }
    }

    /// Determines whether the lock is poisoned.
    ///
    /// If another thread is active, the lock can still become poisoned at any
    /// time. You should not trust a `false` value for program correctness
    /// without additional synchronization.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::{sync::Barrier, thread};
    /// let barrier = Barrier::new(2);
    /// let slice = SliceRwLock::from_vec(vec![0, 1 ,2]);
    /// let (first_elem, mut slice) = slice.split_first().unwrap();
    ///
    /// let handle = thread::scope(|s| {
    ///     let handle = s.spawn(|| {
    ///         let guard = slice.write().unwrap();
    ///         barrier.wait();
    ///         // Checked that the lock is not poisoned in the main thread.
    ///         barrier.wait();
    ///         panic!()
    ///     });
    ///
    ///     // Created `guard` in the spawned thread.
    ///     barrier.wait();
    ///     assert!(!first_elem.is_poisoned());
    ///     barrier.wait();
    ///     // Panicked in the spawned thread.
    ///     handle.join();
    ///     assert!(first_elem.is_poisoned());
    /// });
    /// ```
    #[inline]
    pub fn is_poisoned(&self) -> bool {
        // By construction, `allocation` points to live and valid data.
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }
            .state
            .is_poisoned()
    }

    /// Clear the poisoned state from the allocation guarded by this lock.
    ///
    /// If the lock is poisoned, it will remain poisoned until this function is called by any lock guarding the same allocation. This allows
    /// recovering from a poisoned state and marking that it has recovered. For example, if the
    /// elements are overwritten by known-good values, then the lock can be marked as un-poisoned. Or
    /// possibly, the elements could be inspected to determine if they are in a consistent state, and if
    /// so the poison is removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// # use std::thread;
    /// let slice = SliceRwLock::from_vec(vec![0, 1, 2]);
    /// let (mut first_elem, mut slice) = slice.split_first().unwrap();
    ///
    /// thread::scope(|s| {
    ///     s.spawn(|| {
    ///         let guard = slice.write().unwrap();
    ///         panic!();
    ///     }).join();
    ///
    ///     assert!(first_elem.is_poisoned());
    ///
    ///     first_elem.clear_poison();
    ///     assert!(!first_elem.is_poisoned());
    /// });
    /// ```
    #[inline]
    pub fn clear_poison(&self) {
        // By construction, `allocation` points to live and valid data.
        unsafe { Allocation::get_metadata_disjoint(self.inner.allocation) }
            .state
            .clear_poison();
    }
}

impl<T, A: Allocator> ElemRwLock<MaybeUninit<T>, A> {
    /// Converts to `ElemRwLock<T, A>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the inner value
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: mem::MaybeUninit::assume_init
    ///
    /// # Examples
    ///
    /// ```
    /// # use slice_rw_lock::SliceRwLock;
    /// let slice = SliceRwLock::new_uninit(3);
    /// let (mut first_elem, slice) = slice.split_first().unwrap();
    ///
    /// first_elem.write().unwrap().write(12);
    /// // SAFETY: Initialized the element above.
    /// let first_elem = unsafe { first_elem.assume_init() };
    /// ```
    pub const unsafe fn assume_init(self) -> ElemRwLock<T, A> {
        // SAFETY: All fields of `self` are forgotten immediately after
        // reading them out of the pointers.
        let allocator = unsafe { (&raw const self.allocator).read() };
        let inner = unsafe { (&raw const self.inner).read() };
        mem::forget(self);

        let (ptr, len) = inner.allocation.to_raw_parts();
        ElemRwLock {
            allocator,
            inner: InnerElemRwLock {
                idx: inner.idx,
                allocation: NonNull::from_raw_parts(ptr, len),
            },
        }
    }
}

impl<T, A: Allocator> Drop for ElemRwLock<T, A> {
    fn drop(&mut self) {
        // SAFETY: By construction, every increment of the counter is paired with exactly one decrement.
        // The existance of `self` guarantees that the counter is at least 1.
        // By construction, `allocation` points to live and valid data.
        unsafe {
            Allocation::drop_in_unchecked(self.inner.allocation, &self.allocator);
        }
    }
}

impl<T: Debug, A: Allocator> Debug for ElemRwLock<T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("ElemRwLock");
        match self.try_read_all() {
            Ok(guard) => {
                d.field("data", &&*guard);
            }
            Err(TryLockError::Poisoned(err)) => {
                d.field("data", &&**err.get_ref());
            }
            Err(TryLockError::WouldBlock) => {
                d.field("data", &format_args!("<locked>"));
            }
        }
        d.field("idx", &self.inner.idx);
        d.field("poisoned", &self.is_poisoned());
        d.finish_non_exhaustive()
    }
}

unsafe impl<T: Send + Sync, A: Allocator> Send for ElemRwLock<T, A> {}

impl<T, A: Allocator> RefUnwindSafe for ElemRwLock<T, A> {}

impl<T, A: Allocator> UnwindSafe for ElemRwLock<T, A> {}
