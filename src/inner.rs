pub(crate) use {alloc::Allocation, rw_lock::InnerRwLock, state::State};

#[cold]
#[inline(always)]
pub(crate) fn unlikely(val: bool) -> bool {
    val
}

#[cold]
#[inline(always)]
pub(crate) fn cold_path() {}

mod alloc {
    use super::Metadata;
    use std::{
        alloc::{AllocError, Allocator, Layout, LayoutError, handle_alloc_error},
        mem::{MaybeUninit, needs_drop},
        ptr::{self, NonNull},
        sync::atomic::{self, Ordering},
    };

    #[repr(C)]
    pub(crate) struct Allocation<T> {
        pub(crate) metadata: Metadata,
        pub(crate) slice: [T],
    }

    impl<T> Allocation<T> {
        /// Returns the layout that describes an `Allocation<T, A>`
        #[inline]
        fn get_layout(len: usize) -> Result<Layout, LayoutError> {
            Layout::new::<Metadata>()
                .pad_to_align()
                .extend(Layout::array::<T>(len)?)
                .map(|(layout, _)| layout)
        }

        /// Deallocates the memory referenced by `ptr` in the provided allocator.
        ///
        /// # Safety
        ///
        /// See [`std::alloc::Allocator::deallocate`].
        pub(crate) unsafe fn deallocate_in<A: Allocator>(ptr: NonNull<Self>, allocator: &A) {
            // SAFETY: User-upheld invariants.
            unsafe {
                let layout = Layout::for_value(&*ptr.as_ptr());
                (&raw mut (*ptr.as_ptr()).metadata).drop_in_place();
                if needs_drop::<T>() {
                    (&raw mut (*ptr.as_ptr()).slice).drop_in_place();
                }
                allocator.deallocate(ptr.cast(), layout);
            }
        }

        /// Decrements the reference counter and deallolcates the pointee if the counter becomes nil
        /// without checking whether the counter is non-zero before the decrement.
        ///
        /// # Safety
        ///
        /// See [`LockState::fetch_decrement_counter_unchecked`] and [`Allocation::deallocate_in`]
        pub(crate) unsafe fn drop_in_unchecked<A: Allocator>(ptr: NonNull<Self>, allocator: &A) {
            if unsafe {
                Allocation::get_metadata_disjoint(ptr)
                    .state
                    .fetch_decrement_counter_unchecked(Ordering::Release)
            } == 1
            {
                atomic::fence(Ordering::Acquire);
                unsafe {
                    Allocation::deallocate_in(ptr, allocator);
                }
            }
        }

        /// Returns a pointer to the slice part of the allocation pointedf to by `ptr`.
        ///
        /// # Safety
        ///
        /// `ptr` must point to a valid and live instance of `Allocation<T>`.
        #[inline]
        pub(crate) unsafe fn get_slice(ptr: NonNull<Self>) -> NonNull<[T]> {
            unsafe {
                // SAFETY: A raw pointer to a field is never null.
                NonNull::new_unchecked(
                    // SAFETY: User-upheld invariant.
                    &raw mut (*ptr.as_ptr()).slice,
                )
            }
        }

        /// Returns the length of the underlying slice pointed to by `ptr`..
        pub(crate) const fn len(ptr: NonNull<Self>) -> usize {
            ptr.to_raw_parts().1
        }

        /// Returns whether there exists only a single guard to the allocation.
        ///
        /// # Safety
        ///
        /// `ptr` must point to a valid instance of `Allocation<T>`
        #[inline]
        pub(crate) unsafe fn is_exclusive(ptr: NonNull<Self>) -> bool {
            // SAFETY: User-upheld invariant.
            1 == unsafe { Self::get_metadata_disjoint(ptr).state.get_counter() }
        }

        /// Returns a reference to the metadata of the `Allocation` referenced by `ptr`
        /// without constructing a reference to the whole object.
        ///
        /// # Safety
        ///
        /// `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        #[inline]
        pub(crate) const unsafe fn get_metadata_disjoint<'a>(ptr: NonNull<Self>) -> &'a Metadata {
            unsafe { &(*ptr.as_ptr()).metadata }
        }

        /// Returns a reference to the whole slice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_slice_disjoint<'a>(ptr: NonNull<Self>) -> &'a [T] {
            // SAFETY: User-upheld invariants.
            unsafe { &(*ptr.as_ptr()).slice }
        }

        /// Returns a mutable reference to the whole slice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_slice_mut_disjoint<'a>(ptr: NonNull<Self>) -> &'a mut [T] {
            // SAFETY: User-upheld invariants.
            unsafe { &mut (*ptr.as_ptr()).slice }
        }

        /// Returns a reference to a subslice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_subslice_disjoint<'a>(ptr: NonNull<Self>, start: usize, len: usize) -> &'a [T] {
            // SAFETY: User-upheld invariants.
            unsafe { &*ptr::from_raw_parts((&raw const (*ptr.as_ptr()).slice).cast::<T>().add(start), len) }
        }

        /// Returns a mutable reference to a subslice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_subslice_mut_disjoint<'a>(
            ptr: NonNull<Self>,
            start: usize,
            len: usize,
        ) -> &'a mut [T] {
            // SAFETY: User-upheld invariants.
            unsafe { &mut *ptr::from_raw_parts_mut((&raw mut (*ptr.as_ptr()).slice).cast::<T>().add(start), len) }
        }

        /// Returns a reference to a chunk of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_array_disjoint<'a, const N: usize>(
            ptr: NonNull<Self>,
            start: usize,
        ) -> &'a [T; N] {
            // SAFETY: User-upheld invariants.
            unsafe { &*(&raw const (*ptr.as_ptr()).slice).cast::<T>().add(start).cast() }
        }

        /// Returns a mutable reference to a chunk of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_array_mut_disjoint<'a, const N: usize>(
            ptr: NonNull<Self>,
            start: usize,
        ) -> &'a mut [T; N] {
            // SAFETY: User-upheld invariants.
            unsafe { &mut *(&raw mut (*ptr.as_ptr()).slice).cast::<T>().add(start).cast() }
        }

        /// Returns a reference to an element of the slice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_elem_disjoint<'a>(ptr: NonNull<Self>, idx: usize) -> &'a T {
            // SAFETY: User-upheld invariants.
            unsafe { &*(&raw const (*ptr.as_ptr()).slice).cast::<T>().add(idx) }
        }

        /// Returns a mutable reference to an element of the slice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object.
        ///
        /// # Safety
        ///
        /// * `ptr` must point to a valid instance of `Allocation<T>` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_elem_mut_disjoint<'a>(ptr: NonNull<Self>, idx: usize) -> &'a mut T {
            // SAFETY: User-upheld invariants.
            unsafe { &mut *(&raw mut (*ptr.as_ptr()).slice).cast::<T>().add(idx) }
        }
    }

    impl<T> Allocation<MaybeUninit<T>> {
        /// Allocates an instance of an `Allocation` with uninitialized contents in the provided allocator.
        pub(crate) fn allocate_uninit_in<A: Allocator>(len: usize, allocator: &A) -> NonNull<Self> {
            let layout = Self::get_layout(len).unwrap();
            let ptr = NonNull::<Self>::from_raw_parts(
                allocator
                    .allocate(layout)
                    .unwrap_or_else(|_| handle_alloc_error(layout))
                    .cast::<()>(),
                len,
            );
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it.
            unsafe {
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata::new());
            }
            ptr
        }

        /// Allocates an instance of an `Allocation` with uninitialized contents in the provided allocator,
        /// returning an error if the allocation fails.
        pub(crate) fn try_allocate_uninit_in<A: Allocator>(
            len: usize,
            allocator: &A,
        ) -> Result<NonNull<Self>, AllocError> {
            let layout = match Self::get_layout(len) {
                Ok(layout) => layout,
                Err(_) => return Err(AllocError),
            };
            let ptr = NonNull::<Self>::from_raw_parts(allocator.allocate(layout)?.cast::<()>(), len);
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it.
            unsafe {
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata::new());
            }
            Ok(ptr)
        }

        /// Allocates an instance of an `Allocation` with uninitialized contents,
        /// with the `slice` field being filled with `0` bytes in the provided allocator.
        pub(crate) fn allocate_zeroed_in<A: Allocator>(len: usize, allocator: &A) -> NonNull<Self> {
            let layout = Self::get_layout(len).unwrap();
            let ptr = NonNull::<Self>::from_raw_parts(
                allocator
                    .allocate_zeroed(layout)
                    .unwrap_or_else(|_| handle_alloc_error(layout))
                    .cast::<()>(),
                len,
            );
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it.
            unsafe {
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata::new());
            }
            ptr
        }

        /// Allocates an instance of an `Allocation` with uninitialized contents,
        /// with the `slice` field being filled with `0` bytes in the provided allocator,
        /// returning an error if allocation fails.
        pub(crate) fn try_allocate_zeroed_in<A: Allocator>(
            len: usize,
            allocator: &A,
        ) -> Result<NonNull<Self>, AllocError> {
            let layout = match Self::get_layout(len) {
                Ok(layout) => layout,
                Err(_) => return Err(AllocError),
            };
            let ptr = NonNull::<Self>::from_raw_parts(allocator.allocate_zeroed(layout)?.cast::<()>(), len);
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it.
            unsafe {
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata::new());
            }
            Ok(ptr)
        }
    }
}

mod rw_lock {
    use std::{
        hint, process,
        sync::atomic::{AtomicU32, Ordering},
    };

    pub(crate) struct InnerRwLock(AtomicU32);

    impl InnerRwLock {
        const STATE_MASK: u32 = 1;
        const COUNTER_MASK: u32 = !Self::STATE_MASK;
        const COUNTER_ONE: u32 = 1 << Self::STATE_MASK.count_ones();
        const EMPTY: u32 = 0;
        const ALL_READERS_STATE: u32 = 0;
        const WRITERS_STATE: u32 = 1;
        const ALL_WRITER: u32 = 1;
        pub(crate) const GUARDS_COUNT_MAX: u32 = u32::MAX >> Self::STATE_MASK.count_ones();

        /// Constructs a new unlocked `InnerRwLock`.
        pub(crate) const fn new() -> Self {
            Self(AtomicU32::new(Self::EMPTY))
        }

        /// Blocks until global read access can be granted.
        ///
        /// # Aborts
        ///
        /// Aborts the process on overflow of the guard counter.
        pub(crate) fn read_all(&self) {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                if loaded == Self::EMPTY {
                    match self.0.compare_exchange_weak(
                        Self::EMPTY,
                        Self::ALL_READERS_STATE | Self::COUNTER_ONE,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else if loaded & Self::STATE_MASK == Self::ALL_READERS_STATE && loaded & Self::COUNTER_MASK != 0 {
                    let counter = loaded >> Self::STATE_MASK.count_ones();
                    if crate::inner::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                        process::abort();
                    }
                    match self.0.compare_exchange_weak(
                        loaded,
                        // SAFETY: Checked above that an overflow cannot occur.
                        unsafe { loaded.unchecked_add(Self::COUNTER_ONE) },
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else {
                    atomic_wait::wait(&self.0, loaded);
                    loaded = self.0.load(Ordering::Relaxed);
                }
            }
        }

        /// Attempts to acquire global read access without blocking. Returns whether the operation succeeded.
        ///
        /// # Aborts
        ///
        /// Aborts the process on overflow of the guard counter.
        pub(crate) fn try_read_all(&self) -> bool {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                if loaded == Self::EMPTY {
                    match self.0.compare_exchange_weak(
                        Self::EMPTY,
                        Self::ALL_READERS_STATE | Self::COUNTER_ONE,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else if loaded & Self::STATE_MASK == Self::ALL_READERS_STATE && loaded & Self::COUNTER_MASK != 0 {
                    let counter = loaded >> Self::STATE_MASK.count_ones();
                    if crate::inner::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                        process::abort();
                    }
                    match self.0.compare_exchange_weak(
                        loaded,
                        // SAFETY: Checked above that an overflow cannot occur.
                        unsafe { loaded.unchecked_add(Self::COUNTER_ONE) },
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else {
                    return false;
                }
            }
        }

        /// Blocks until disjoint write access can be granted.
        ///
        /// # Aborts
        ///
        /// Aborts the process on overflow of the guard counter.
        pub(crate) fn write(&self) {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                if loaded == Self::EMPTY {
                    match self.0.compare_exchange_weak(
                        Self::EMPTY,
                        Self::WRITERS_STATE | Self::COUNTER_ONE,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else if loaded & Self::STATE_MASK == Self::WRITERS_STATE && loaded & Self::COUNTER_MASK != 0 {
                    let counter = loaded >> Self::STATE_MASK.count_ones();
                    if crate::inner::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                        process::abort();
                    }
                    match self.0.compare_exchange_weak(
                        loaded,
                        // SAFETY: Checked above that an overflow cannot occur.
                        unsafe { loaded.unchecked_add(Self::COUNTER_ONE) },
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else {
                    atomic_wait::wait(&self.0, loaded);
                    loaded = self.0.load(Ordering::Relaxed);
                }
            }
        }

        /// Attempts to acquire disjoint write access without blocking. Returns whether the operation succeeded.
        ///
        /// # Aborts
        ///
        /// Aborts the process on overflow of the guard counter.
        pub(crate) fn try_write(&self) -> bool {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                if loaded == Self::EMPTY {
                    match self.0.compare_exchange_weak(
                        Self::EMPTY,
                        Self::WRITERS_STATE | Self::COUNTER_ONE,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else if loaded & Self::STATE_MASK == Self::WRITERS_STATE && loaded & Self::COUNTER_MASK != 0 {
                    let counter = loaded >> Self::STATE_MASK.count_ones();
                    if crate::inner::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                        process::abort()
                    }
                    match self.0.compare_exchange_weak(
                        loaded,
                        // SAFETY: Checked above that an overflow cannot occur.
                        unsafe { loaded.unchecked_add(Self::COUNTER_ONE) },
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else {
                    return false;
                }
            }
        }

        /// Blocks until global write access can be granted.
        pub(crate) fn write_all(&self) {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                if loaded == Self::EMPTY {
                    match self.0.compare_exchange_weak(
                        Self::EMPTY,
                        Self::ALL_WRITER,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else {
                    atomic_wait::wait(&self.0, loaded);
                    loaded = self.0.load(Ordering::Relaxed);
                }
            }
        }

        /// Attempts to acquire global write access without blocking. Returns whether the operation succeeded.
        pub(crate) fn try_write_all(&self) -> bool {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                if loaded == Self::EMPTY {
                    match self.0.compare_exchange_weak(
                        Self::EMPTY,
                        Self::ALL_WRITER,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                } else {
                    return false;
                }
            }
        }

        /// Decrements the global readers counter, assuming it is not nil.
        ///
        /// # Safety
        ///
        /// There must be at least one global reader alive when this function is called.
        pub(crate) unsafe fn drop_all_reader_unchecked(&self) {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                let counter = loaded >> Self::STATE_MASK.count_ones();
                match self.0.compare_exchange_weak(
                    loaded,
                    if counter == 0 {
                        // SAFETY: User-upheld invariant
                        unsafe { hint::unreachable_unchecked() }
                    } else if counter == 1 {
                        Self::EMPTY
                    } else {
                        // SAFETY: Checked above that overflow cannot occur, assuming the invariant holds.
                        unsafe { loaded.unchecked_sub(Self::COUNTER_ONE) }
                    },
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        atomic_wait::wake_all(&self.0);
                        return;
                    }
                    Err(current) => {
                        loaded = current;
                        hint::spin_loop();
                    }
                }
            }
        }

        /// Decrements the disjoint writers counter, assuming it is not nil.
        ///
        /// # Safety
        ///
        /// There must be at least one disjoint writer alive when this function is called.
        pub(crate) unsafe fn drop_writer_unchecked(&self) {
            let mut loaded = self.0.load(Ordering::Relaxed);
            loop {
                let counter = loaded >> Self::STATE_MASK.count_ones();
                match self.0.compare_exchange_weak(
                    loaded,
                    if counter == 0 {
                        // SAFETY: User-upheld invariant.
                        unsafe { hint::unreachable_unchecked() }
                    } else if counter == 1 {
                        Self::EMPTY
                    } else {
                        // SAFETY: Checked above that overflow cannot occur, assuming the invariant holds.
                        unsafe { loaded.unchecked_sub(Self::COUNTER_ONE) }
                    },
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        atomic_wait::wake_all(&self.0);
                        return;
                    }
                    Err(current) => {
                        loaded = current;
                        hint::spin_loop();
                    }
                }
            }
        }

        /// Decrements the global writers counter, assuming it is not nil.
        ///
        /// # Safety
        ///
        /// There must be a global writer alive when this function is called.
        pub(crate) unsafe fn drop_all_writer_unchecked(&self) {
            self.0.store(Self::EMPTY, Ordering::Release);
            atomic_wait::wake_all(&self.0);
        }

        #[cfg(feature = "downgrade")]
        /// Changes the state of the lock from global write to global read, assuming it is in the former.
        ///
        /// # Safety
        ///
        /// There must be a global writer alive when this function is called.
        pub(crate) unsafe fn downgrade_unchecked(&self) {
            self.0
                .store(Self::ALL_READERS_STATE | Self::COUNTER_ONE, Ordering::Release);
            atomic_wait::wake_all(&self.0);
        }

        #[cfg(feature = "downgrade")]
        /// Changes the state of the lock from global write to write, assuming it is in the former.
        ///
        /// # Safety
        ///
        /// There must be a global writer alive when this function is called.
        pub(crate) unsafe fn downgrade_write_unchecked(&self) {
            self.0.store(Self::WRITERS_STATE | Self::COUNTER_ONE, Ordering::Release);
            atomic_wait::wake_all(&self.0);
        }
    }

    #[cfg(test)]
    mod tests {
        use super::InnerRwLock;
        use std::{num::NonZeroU32, sync::atomic::Ordering};

        const ONE: NonZeroU32 = NonZeroU32::new(1).unwrap();
        const TWO: NonZeroU32 = NonZeroU32::new(2).unwrap();

        #[derive(Debug)]
        pub(crate) enum LockState {
            Empty,
            AllReaders(NonZeroU32),
            Writers(NonZeroU32),
            AllWriter,
        }

        impl InnerRwLock {
            pub(crate) fn state(&self) -> LockState {
                match self.0.load(Ordering::Relaxed) {
                    Self::EMPTY => LockState::Empty,
                    Self::ALL_WRITER => LockState::AllWriter,
                    loaded => {
                        let counter = unsafe { NonZeroU32::new_unchecked(loaded >> Self::STATE_MASK.count_ones()) };
                        if loaded & Self::STATE_MASK == Self::WRITERS_STATE {
                            LockState::Writers(counter)
                        } else {
                            LockState::AllReaders(counter)
                        }
                    }
                }
            }

            pub(crate) fn reset(&self) {
                self.0.store(Self::EMPTY, Ordering::Relaxed);
            }
        }

        mod single_threaded {
            use super::{super::InnerRwLock, LockState, ONE, TWO};
            use std::assert_matches::assert_matches;

            #[test]
            fn read_all() {
                let lock = InnerRwLock::new();

                lock.read_all();
                assert_matches!(lock.state(), LockState::AllReaders(ONE));

                unsafe {
                    lock.drop_all_reader_unchecked();
                }
                assert_matches!(lock.state(), LockState::Empty);

                lock.read_all();

                assert!(lock.try_read_all());
                assert_matches!(lock.state(), LockState::AllReaders(TWO));

                unsafe {
                    lock.drop_all_reader_unchecked();
                }
                assert_matches!(lock.state(), LockState::AllReaders(ONE));

                assert!(!lock.try_write());
                assert_matches!(lock.state(), LockState::AllReaders(ONE));

                assert!(!lock.try_write_all());
                assert_matches!(lock.state(), LockState::AllReaders(ONE));
            }

            #[test]
            fn write() {
                let lock = InnerRwLock::new();

                lock.write();
                assert_matches!(lock.state(), LockState::Writers(ONE));

                unsafe {
                    lock.drop_writer_unchecked();
                }
                assert_matches!(lock.state(), LockState::Empty);

                lock.write();

                assert!(lock.try_write());
                assert_matches!(lock.state(), LockState::Writers(TWO));

                unsafe {
                    lock.drop_writer_unchecked();
                }
                assert_matches!(lock.state(), LockState::Writers(ONE));

                assert!(!lock.try_read_all());
                assert_matches!(lock.state(), LockState::Writers(ONE));

                assert!(!lock.try_write_all());
                assert_matches!(lock.state(), LockState::Writers(ONE));
            }

            #[test]
            fn write_all() {
                let lock = InnerRwLock::new();

                lock.write_all();
                assert_matches!(lock.state(), LockState::AllWriter);

                unsafe {
                    lock.drop_all_writer_unchecked();
                }
                assert_matches!(lock.state(), LockState::Empty);

                lock.write_all();

                assert!(!lock.try_read_all());
                assert_matches!(lock.state(), LockState::AllWriter);

                assert!(!lock.try_write());
                assert_matches!(lock.state(), LockState::AllWriter);

                assert!(!lock.try_write_all());
                assert_matches!(lock.state(), LockState::AllWriter);
            }

            #[cfg(feature = "downgrade")]
            #[test]
            fn downgrade() {
                let lock = InnerRwLock::new();
                lock.write_all();

                unsafe {
                    lock.downgrade_unchecked();
                }
                assert_matches!(lock.state(), LockState::AllReaders(ONE));

                lock.reset();
                lock.write_all();

                unsafe {
                    lock.downgrade_write_unchecked();
                }
                assert_matches!(lock.state(), LockState::Writers(ONE));
            }
        }

        mod concurrent {
            use super::{super::InnerRwLock, LockState, ONE, TWO};
            use std::{assert_matches::assert_matches, sync::Barrier, thread};

            #[test]
            fn read_all() {
                let lock = InnerRwLock::new();
                let barrier = Barrier::new(2);

                thread::scope(|s| {
                    s.spawn(|| {
                        // ..0
                        barrier.wait();
                        // 1
                        assert_matches!(lock.state(), LockState::AllReaders(ONE));

                        unsafe {
                            lock.drop_all_reader_unchecked();
                        }
                        barrier.wait();
                        // ...2
                        barrier.wait();
                        // 3
                        assert_matches!(lock.state(), LockState::AllReaders(TWO));

                        unsafe {
                            lock.drop_all_reader_unchecked();
                        }
                        barrier.wait();
                        // ...4
                        barrier.wait();
                        // 5
                        assert_matches!(lock.state(), LockState::AllReaders(ONE));

                        assert!(!lock.try_write_all());
                        barrier.wait();
                    });

                    // 0
                    lock.read_all();
                    barrier.wait();
                    // ...1
                    barrier.wait();
                    // 2
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.read_all();

                    assert!(lock.try_read_all());
                    barrier.wait();
                    // ...3
                    barrier.wait();
                    // 4
                    assert_matches!(lock.state(), LockState::AllReaders(ONE));

                    assert!(!lock.try_write());
                    barrier.wait();
                    // ...5
                    barrier.wait();
                    // 6
                    assert_matches!(lock.state(), LockState::AllReaders(ONE));
                });
            }

            #[test]
            fn write() {
                let lock = InnerRwLock::new();
                let barrier = Barrier::new(2);

                thread::scope(|s| {
                    s.spawn(|| {
                        // ..0
                        barrier.wait();
                        // 1
                        assert_matches!(lock.state(), LockState::Writers(ONE));

                        unsafe {
                            lock.drop_writer_unchecked();
                        }
                        barrier.wait();
                        // ...2
                        barrier.wait();
                        // 3
                        assert_matches!(lock.state(), LockState::Writers(TWO));

                        unsafe {
                            lock.drop_writer_unchecked();
                        }
                        barrier.wait();
                        // ...4
                        barrier.wait();
                        // 5
                        assert_matches!(lock.state(), LockState::Writers(ONE));

                        assert!(!lock.try_write_all());
                        barrier.wait();
                    });

                    // 0
                    lock.write();
                    barrier.wait();
                    // ...1
                    barrier.wait();
                    // 2
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.write();

                    assert!(lock.try_write());
                    barrier.wait();
                    // ...3
                    barrier.wait();
                    // 4
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    assert!(!lock.try_read_all());
                    barrier.wait();
                    // ...5
                    barrier.wait();
                    // 6
                    assert_matches!(lock.state(), LockState::Writers(ONE));
                });
            }

            #[test]
            fn write_all() {
                let lock = InnerRwLock::new();
                let barrier = Barrier::new(2);

                thread::scope(|s| {
                    s.spawn(|| {
                        // ..0
                        barrier.wait();
                        // 1
                        assert_matches!(lock.state(), LockState::AllWriter);

                        unsafe {
                            lock.drop_all_writer_unchecked();
                        }
                        barrier.wait();
                        // ...2
                        barrier.wait();
                        // 3
                        assert_matches!(lock.state(), LockState::AllWriter);

                        assert!(!lock.try_write());
                        barrier.wait();
                        // ...4
                        barrier.wait();
                        // 5
                        assert_matches!(lock.state(), LockState::AllWriter);
                    });

                    // 0
                    lock.write_all();
                    barrier.wait();
                    // ...1
                    barrier.wait();
                    // 2
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.write_all();

                    assert!(!lock.try_read_all());
                    barrier.wait();
                    // ...3
                    barrier.wait();
                    // 4
                    assert_matches!(lock.state(), LockState::AllWriter);

                    assert!(!lock.try_write_all());
                    barrier.wait();
                });
            }

            #[cfg(feature = "downgrade")]
            #[test]
            fn downgrade() {
                let lock = InnerRwLock::new();
                let barrier = Barrier::new(2);

                thread::scope(|s| {
                    s.spawn(|| {
                        // ...0
                        barrier.wait();
                        // 1
                        assert_matches!(lock.state(), LockState::AllReaders(ONE));

                        lock.reset();
                        lock.write_all();
                        unsafe {
                            lock.downgrade_write_unchecked();
                        }
                        barrier.wait();
                    });

                    // 0
                    lock.write_all();

                    unsafe {
                        lock.downgrade_unchecked();
                    }
                    barrier.wait();
                    // ...1
                    barrier.wait();
                    // 2
                    assert_matches!(lock.state(), LockState::Writers(ONE));
                });
            }
        }
    }
}

mod state {
    use std::sync::atomic::{AtomicU32, Ordering};

    pub(crate) struct State(AtomicU32);

    impl State {
        const POISONED: u32 = 1;
        const COUNTER_ONE: u32 = 1 << Self::POISONED.count_ones();
        pub(crate) const MAX_COUNT: u32 = u32::MAX >> Self::POISONED.count_ones();

        /// Constructs a `LockState`, initialized to "not poisoned" and "no locks".
        #[inline]
        pub(super) const fn new() -> Self {
            Self(AtomicU32::new(0))
        }

        /// Returns whether the lock is poisoned (`Relaxed` ordering).
        #[inline]
        pub(crate) fn is_poisoned(&self) -> bool {
            self.0.load(Ordering::Relaxed) & Self::POISONED != 0
        }

        /// Clears poison from lock (`Relaxed` ordering).
        #[inline]
        pub(crate) fn clear_poison(&self) {
            self.0.fetch_and(!Self::POISONED, Ordering::Relaxed);
        }

        /// Poisons the lock (`Relaxed` ordering).
        #[inline]
        pub(crate) fn poison(&self) {
            self.0.fetch_or(Self::POISONED, Ordering::Relaxed);
        }

        /// Returns the number of locks alive (`Relaxed` ordering).
        #[inline]
        pub(crate) fn get_counter(&self) -> u32 {
            self.0.load(Ordering::Relaxed) >> Self::POISONED.count_ones()
        }

        /// Increments the locks counter and returns the previous value, assuming overflow cannot occur.
        ///
        /// # Safety
        ///
        /// The counter must not overflow.
        #[inline]
        pub(crate) unsafe fn fetch_increment_counter_unchecked(&self, order: Ordering) -> u32 {
            self.0.fetch_add(Self::COUNTER_ONE, order) >> Self::POISONED.count_ones()
        }

        /// Decrements the locks counter and returns the previous value, assuming overflow cannot occur.
        ///
        /// # Safety
        ///
        /// The counter must not underflow.
        #[inline]
        pub(crate) unsafe fn fetch_decrement_counter_unchecked(&self, order: Ordering) -> u32 {
            self.0.fetch_sub(Self::COUNTER_ONE, order) >> Self::POISONED.count_ones()
        }
    }

    #[cfg(test)]
    mod tests {
        mod single_threaded {
            use super::super::State;
            use std::sync::atomic::Ordering;

            #[test]
            fn poison() {
                let state = State::new();

                state.poison();
                assert!(state.is_poisoned());

                state.clear_poison();
                assert!(!state.is_poisoned());
            }

            #[test]
            fn counter() {
                let state = State::new();

                assert_eq!(unsafe { state.fetch_increment_counter_unchecked(Ordering::Relaxed) }, 0);
                assert_eq!(state.get_counter(), 1);

                assert_eq!(unsafe { state.fetch_decrement_counter_unchecked(Ordering::Relaxed) }, 1);
                assert_eq!(state.get_counter(), 0);
            }
        }

        mod concurrent {
            use super::super::State;
            use std::{
                sync::{Barrier, atomic::Ordering},
                thread,
            };

            #[test]
            fn poison() {
                let state = State::new();
                let barrier = Barrier::new(2);

                thread::scope(|s| {
                    s.spawn(|| {
                        // ...0
                        barrier.wait();
                        // 1
                        assert!(state.is_poisoned());

                        state.clear_poison();
                        barrier.wait();
                    });

                    // 0
                    state.poison();
                    barrier.wait();
                    // ...1
                    barrier.wait();
                    assert!(!state.is_poisoned());
                });
            }

            #[test]
            fn counter() {
                let state = State::new();
                let barrier = Barrier::new(2);

                thread::scope(|s| {
                    s.spawn(|| {
                        // ...0
                        barrier.wait();
                        // 1
                        assert_eq!(state.get_counter(), 1);

                        assert_eq!(unsafe { state.fetch_decrement_counter_unchecked(Ordering::Relaxed) }, 1);
                        barrier.wait();
                    });

                    // 0
                    assert_eq!(unsafe { state.fetch_increment_counter_unchecked(Ordering::Relaxed) }, 0);
                    barrier.wait();
                    // ...1
                    barrier.wait();
                    // 2
                    assert_eq!(state.get_counter(), 0);
                });
            }
        }
    }
}

pub(crate) struct Metadata {
    pub(crate) lock: InnerRwLock,
    pub(crate) state: State,
}

impl Metadata {
    pub(crate) fn new() -> Self {
        Self {
            lock: InnerRwLock::new(),
            state: State::new(),
        }
    }
}

mod full_rw_lock {
    mod atomic_wait_parking {
        use std::{
            hint, process,
            sync::atomic::{self, AtomicU32, Ordering},
        };

        pub(crate) struct InnerRwLock(AtomicU32);

        impl InnerRwLock {
            const FLAG_MASK: u32 = 1u32;
            const FIRST_COUNTER_MASK: u32 = {
                const FIRST_COUNTER_BITS: u32 = u32::BITS / 2;
                const FIRST_BIT: u32 = 1;
                let mut res = 0;
                let mut i = 0;
                while i < FIRST_COUNTER_BITS {
                    res <<= 1;
                    res += FIRST_BIT;
                    i += 1;
                }
                res << Self::FLAG_MASK.count_ones()
            };
            const SECOND_COUNTER_MASK: u32 = { !0 & !Self::FLAG_MASK & !Self::FIRST_COUNTER_MASK };
            const FIRST_COUNTER_ONE: u32 = 1 << Self::FIRST_COUNTER_MASK.trailing_zeros();
            const SECOND_COUNTER_ONE: u32 = 1 << Self::SECOND_COUNTER_MASK.trailing_zeros();
            const FLAG_TRUE: u32 = Self::FLAG_MASK;
            const EMPTY: u32 = 0;
            const GLOBAL_WRITER: u32 = Self::FLAG_TRUE;

            pub(crate) const fn new() -> Self {
                Self(AtomicU32::new(Self::EMPTY))
            }

            pub(crate) fn read(&self) {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded == Self::GLOBAL_WRITER {
                        atomic_wait::wait(&self.0, loaded);
                        loaded = self.0.load(Ordering::Relaxed);
                    } else if crate::inner::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
                        process::abort();
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the first counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::FIRST_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_read(&self) -> bool {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded == Self::GLOBAL_WRITER {
                        return false;
                    } else if crate::inner::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
                        process::abort();
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the first counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::FIRST_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn read_all(&self) {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::FLAG_MASK == Self::FLAG_TRUE {
                        atomic_wait::wait(&self.0, loaded);
                        loaded = self.0.load(Ordering::Relaxed);
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort();
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_read_all(&self) -> bool {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::FLAG_MASK == Self::FLAG_TRUE {
                        return false;
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort();
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn write(&self) {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded == Self::GLOBAL_WRITER
                        || (loaded & Self::FLAG_MASK != Self::FLAG_TRUE && loaded & Self::SECOND_COUNTER_MASK != 0)
                    {
                        atomic_wait::wait(&self.0, loaded);
                        loaded = self.0.load(Ordering::Relaxed);
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort();
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            Self::FLAG_TRUE | unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) },
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_write(&self) -> bool {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded == Self::GLOBAL_WRITER
                        || (loaded & Self::FLAG_MASK != Self::FLAG_TRUE && loaded & Self::SECOND_COUNTER_MASK != 0)
                    {
                        return false;
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort();
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) } | Self::FLAG_TRUE,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn write_all(&self) {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded != Self::EMPTY {
                        atomic_wait::wait(&self.0, loaded);
                        loaded = self.0.load(Ordering::Relaxed);
                    } else {
                        match self.0.compare_exchange_weak(
                            Self::EMPTY,
                            Self::GLOBAL_WRITER,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_write_all(&self) -> bool {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if loaded != Self::EMPTY {
                        return false;
                    } else {
                        match self.0.compare_exchange_weak(
                            Self::EMPTY,
                            Self::GLOBAL_WRITER,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) unsafe fn drop_reader_unchecked(&self) {
                if self.0.fetch_sub(Self::FIRST_COUNTER_ONE, Ordering::Release) == Self::FIRST_COUNTER_ONE {
                    atomic::fence(Ordering::Acquire);
                    atomic_wait::wake_one(&self.0);
                }
            }

            pub(crate) unsafe fn drop_global_reader_unchecked(&self) {
                if self.0.fetch_sub(Self::SECOND_COUNTER_ONE, Ordering::Release) & Self::SECOND_COUNTER_MASK
                    == Self::SECOND_COUNTER_ONE
                {
                    atomic::fence(Ordering::Acquire);
                    atomic_wait::wake_all(&self.0);
                }
            }

            pub(crate) unsafe fn drop_writer_unchecked(&self) {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if (loaded & Self::SECOND_COUNTER_MASK) == Self::SECOND_COUNTER_ONE {
                        match self.0.compare_exchange_weak(
                            loaded,
                            loaded & Self::FIRST_COUNTER_MASK,
                            Ordering::AcqRel,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => {
                                atomic_wait::wake_all(&self.0);
                                return;
                            }
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: User-upheld invariant.
                            unsafe { loaded.unchecked_sub(Self::SECOND_COUNTER_ONE) },
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) unsafe fn drop_global_writer_unchecked(&self) {
                self.0.store(Self::EMPTY, Ordering::Release);
                atomic_wait::wake_all(&self.0);
            }

            #[cfg(feature = "downgrade")]
            pub(crate) unsafe fn downgrade_writer_unchecked(&self) {
                let mut loaded = self.0.load(Ordering::Relaxed);
                loop {
                    if crate::inner::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
                        process::abort()
                    } else if loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_ONE {
                        match self.0.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the first counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::FIRST_COUNTER_ONE) } & Self::FIRST_COUNTER_MASK,
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => {
                                atomic::fence(Ordering::Acquire);
                                atomic_wait::wake_all(&self.0);
                                return;
                            }
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    } else {
                        match self.0.compare_exchange_weak(
                            loaded,
                            unsafe {
                                loaded
                                    // SAFETY: User-upheld invariant.
                                    .unchecked_sub(Self::SECOND_COUNTER_ONE)
                                    // SAFETY: Checked above that the first counter can be safely incremented
                                    .unchecked_add(Self::FIRST_COUNTER_ONE)
                            },
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            #[cfg(feature = "downgrade")]
            pub(crate) unsafe fn downgrade_global_writer_unchecked(&self) {
                self.0.store(Self::SECOND_COUNTER_ONE, Ordering::Release);
                atomic_wait::wake_all(&self.0);
            }
        }

        unsafe impl Sync for InnerRwLock {}

        #[cfg(test)]
        mod tests {
            use super::InnerRwLock;
            use std::{hint, num::NonZeroU16, sync::atomic::Ordering};

            const ONE: NonZeroU16 = NonZeroU16::new(1).unwrap();
            const TWO: NonZeroU16 = NonZeroU16::new(2).unwrap();

            #[derive(Debug)]
            pub(crate) enum LockState {
                Empty,
                Readers(NonZeroU16),
                GlobalReaders(NonZeroU16),
                Writers(NonZeroU16),
                GlobalWriter,
                ReadersAndGlobalReaders {
                    readers: NonZeroU16,
                    global_readers: NonZeroU16,
                },
                ReadersAndWriters {
                    readers: NonZeroU16,
                    writers: NonZeroU16,
                },
            }

            impl InnerRwLock {
                pub(crate) fn state(&self) -> LockState {
                    let loaded = self.0.load(Ordering::Relaxed);
                    let first_counter = NonZeroU16::new(
                        ((loaded & Self::FIRST_COUNTER_MASK) >> Self::FIRST_COUNTER_MASK.trailing_zeros()) as _,
                    );
                    let second_counter = NonZeroU16::new(
                        ((loaded & Self::SECOND_COUNTER_MASK) >> Self::SECOND_COUNTER_MASK.trailing_zeros()) as _,
                    );
                    match (
                        loaded & Self::FLAG_MASK == Self::FLAG_TRUE,
                        first_counter,
                        second_counter,
                    ) {
                        (false, None, None) => LockState::Empty,
                        (false, Some(readers), None) => LockState::Readers(readers),
                        (false, None, Some(global_readers)) => LockState::GlobalReaders(global_readers),
                        (true, None, Some(writers)) => LockState::Writers(writers),
                        (true, None, None) => LockState::GlobalWriter,
                        (false, Some(readers), Some(global_readers)) => LockState::ReadersAndGlobalReaders {
                            readers,
                            global_readers,
                        },
                        (true, Some(readers), Some(writers)) => LockState::ReadersAndWriters { readers, writers },
                        (true, Some(_), None) => unsafe { hint::unreachable_unchecked() },
                    }
                }

                pub(crate) fn reset(&self) {
                    self.0.store(Self::EMPTY, Ordering::Relaxed);
                }
            }

            mod single_threaded {
                use super::{super::InnerRwLock, LockState, ONE, TWO};
                use std::assert_matches::assert_matches;

                #[test]
                fn read() {
                    let lock = InnerRwLock::new();

                    lock.read();
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.read();

                    assert!(lock.try_read());
                    assert_matches!(lock.state(), LockState::Readers(TWO));

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    lock.read_all();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndGlobalReaders {
                            readers: ONE,
                            global_readers: ONE
                        }
                    );
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    lock.write();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndWriters {
                            readers: ONE,
                            writers: ONE
                        }
                    );
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::Readers(ONE));
                }

                #[test]
                fn read_all() {
                    let lock = InnerRwLock::new();

                    lock.read_all();
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.read_all();

                    assert!(lock.try_read_all());
                    assert_matches!(lock.state(), LockState::GlobalReaders(TWO));

                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    lock.read();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndGlobalReaders {
                            readers: ONE,
                            global_readers: ONE
                        }
                    );

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    assert!(!lock.try_write());
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                }

                #[test]
                fn write() {
                    let lock = InnerRwLock::new();

                    lock.write();
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.write();

                    assert!(lock.try_write());
                    assert_matches!(lock.state(), LockState::Writers(TWO));

                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    lock.read();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndWriters {
                            readers: ONE,
                            writers: ONE
                        }
                    );

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    assert!(!lock.try_read_all());
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::Writers(ONE));
                }

                #[test]
                fn write_all() {
                    let lock = InnerRwLock::new();

                    lock.write_all();
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    unsafe {
                        lock.drop_global_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.write_all();

                    assert!(!lock.try_read());
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    assert!(!lock.try_read_all());
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    assert!(!lock.try_write());
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::GlobalWriter);
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_writer() {
                    let lock = InnerRwLock::new();
                    lock.write();

                    unsafe {
                        lock.downgrade_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    lock.write();
                    unsafe {
                        lock.downgrade_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(TWO));
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_global_writer() {
                    let lock = InnerRwLock::new();
                    lock.write_all();

                    unsafe {
                        lock.downgrade_global_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                }
            }

            mod concurrent {
                use super::{super::InnerRwLock, LockState, ONE, TWO};
                use std::{assert_matches::assert_matches, sync::Barrier, thread};

                #[test]
                fn read() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ...0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::Readers(ONE));

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::Readers(TWO));

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndGlobalReaders {
                                    readers: ONE,
                                    global_readers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_global_reader_unchecked();
                            }
                            barrier.wait();
                            // ...6
                            barrier.wait();
                            // 7
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndWriters {
                                    readers: ONE,
                                    writers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_writer_unchecked();
                            }
                            barrier.wait();
                            // ...8
                            barrier.wait();
                            // 9
                            assert_matches!(lock.state(), LockState::Readers(ONE));
                        });

                        // 0
                        lock.read();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.read();

                        assert!(lock.try_read());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::Readers(ONE));

                        lock.read_all();
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::Readers(ONE));

                        lock.write();
                        barrier.wait();
                        // ...7
                        barrier.wait();
                        // 8
                        assert_matches!(lock.state(), LockState::Readers(ONE));

                        assert!(!lock.try_write_all());
                        barrier.wait();
                    })
                }

                #[test]
                fn read_all() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ..0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                            unsafe {
                                lock.drop_global_reader_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::GlobalReaders(TWO));

                            unsafe {
                                lock.drop_global_reader_unchecked();
                            }
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndGlobalReaders {
                                    readers: ONE,
                                    global_readers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...6
                            barrier.wait();
                            // 7
                            assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                            assert!(!lock.try_write_all());
                            barrier.wait();
                        });

                        // 0
                        lock.read_all();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.read_all();

                        assert!(lock.try_read_all());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                        lock.read();
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                        assert!(!lock.try_write());
                        barrier.wait();
                        // ...7
                        barrier.wait();
                        // 8
                        assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                    });
                }

                #[test]
                fn write() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ..0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::Writers(ONE));

                            unsafe {
                                lock.drop_writer_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::Writers(TWO));

                            unsafe {
                                lock.drop_writer_unchecked();
                            }
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndWriters {
                                    readers: ONE,
                                    writers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...6
                            barrier.wait();
                            // 7
                            assert_matches!(lock.state(), LockState::Writers(ONE));

                            assert!(!lock.try_write_all());
                            barrier.wait();
                        });

                        // 0
                        lock.write();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.write();

                        assert!(lock.try_write());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::Writers(ONE));

                        lock.read();
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::Writers(ONE));

                        assert!(!lock.try_read_all());
                        barrier.wait();
                        // ...7
                        barrier.wait();
                        // 8
                        assert_matches!(lock.state(), LockState::Writers(ONE));
                    });
                }

                #[test]
                fn write_all() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ..0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::GlobalWriter);

                            unsafe {
                                lock.drop_global_writer_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::GlobalWriter);

                            assert!(!lock.try_read_all());
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(lock.state(), LockState::GlobalWriter);

                            assert!(!lock.try_write_all());
                            barrier.wait();
                        });

                        // 0
                        lock.write_all();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.write_all();

                        assert!(!lock.try_read());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::GlobalWriter);

                        assert!(!lock.try_write());
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::GlobalWriter);
                    });
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_writer() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ...0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::Readers(ONE));

                            lock.write();
                            unsafe {
                                lock.downgrade_writer_unchecked();
                            }
                            barrier.wait();
                        });

                        // 0
                        lock.write();

                        unsafe {
                            lock.downgrade_writer_unchecked();
                        }
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Readers(TWO));
                    })
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_global_writer() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ...0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                        });

                        // 0
                        lock.write_all();

                        unsafe {
                            lock.downgrade_global_writer_unchecked();
                        }
                        barrier.wait();
                    });
                }
            }
        }
    }

    mod std_parking {
        use std::{
            cell::UnsafeCell,
            hint,
            marker::PhantomPinned,
            pin::{Pin, pin},
            process,
            ptr::NonNull,
            sync::atomic::{self, AtomicU8, AtomicU32, Ordering},
            thread::{self, Thread},
        };

        struct Queue {
            head: Option<NonNull<Anchor>>,
            tail: Option<NonNull<Anchor>>,
        }

        struct Anchor {
            next: UnsafeCell<Option<NonNull<Anchor>>>,
            prev: UnsafeCell<Option<NonNull<Anchor>>>,
            handle: Thread,
            status: AtomicU8,
            phantom: PhantomPinned,
        }

        impl Anchor {
            const PARKED: u8 = 0;
            const BUSY: u8 = 1;
            const UNPARKED: u8 = 2;

            fn new() -> Self {
                Self {
                    next: UnsafeCell::new(None),
                    prev: UnsafeCell::new(None),
                    handle: thread::current(),
                    status: AtomicU8::new(Self::UNPARKED),
                    phantom: PhantomPinned,
                }
            }

            /// Wait until another thread wakes this one up.
            ///
            /// # Safety
            ///
            /// There must not exist any mutable references to the anchor at this point.
            unsafe fn wait(self: &Pin<&Self>) {
                while self.status.load(Ordering::Relaxed) == Self::PARKED {
                    thread::park();
                }
                while self.status.load(Ordering::Relaxed) == Self::BUSY {
                    hint::spin_loop();
                }
                atomic::fence(Ordering::Acquire);
            }
        }

        impl Queue {
            /// Creates a new empty queue.
            const fn new() -> Self {
                Self { head: None, tail: None }
            }

            #[inline]
            /// Registers a thread in the queue.
            ///
            /// # Safety
            ///
            /// - The `Anchor` passed to this function must call `wait` before
            ///   any future calls to `enter` with it.
            /// - All Previous and next calls to this function must be valid.
            const unsafe fn enter(&mut self, anchor: Pin<&mut Anchor>) {
                // SAFETY: nothing is moved out of `anchor`.
                let anchor = unsafe { anchor.get_unchecked_mut() };
                anchor.status = AtomicU8::new(Anchor::UNPARKED);
                *anchor.next.get_mut() = None;
                match self {
                    matched @ &mut Queue { head: None, .. } => {
                        let node = Some(NonNull::from_ref(anchor));
                        matched.head = node;
                        matched.tail = node;
                    }
                    Queue {
                        head: Some(_),
                        tail: Some(tail),
                    } => {
                        let node_non_null = NonNull::from_ref(anchor);
                        // SAFETY: The access to the entire queue is exclusive.
                        unsafe {
                            *anchor.prev.get() = Some(*tail);
                            *tail.as_ref().next.get() = Some(node_non_null);
                        }
                        *tail = node_non_null;
                    }
                    // SAFETY: By construction, if `head` is non-null, so is `tail`.
                    _ => unsafe { hint::unreachable_unchecked() },
                }
            }

            #[inline]
            /// Wakse the first thread in the queue.
            ///
            /// # Safety
            ///
            /// All previous calls to `enter` must be valid.
            unsafe fn wake_one(&mut self) {
                if let Some(head) = self.head {
                    // SAFETY: User-upheld invariant.
                    let node = unsafe { head.as_ref() };
                    // SAFETY: The access to the entire queue is exclusive.
                    unsafe {
                        self.head = *node.next.get();
                    }
                    node.status.store(Anchor::BUSY, Ordering::Relaxed);
                    node.handle.unpark();
                    node.status.store(Anchor::UNPARKED, Ordering::Release);
                }
            }

            /// Wakes all the threads in the queue.
            ///
            /// # Safety
            ///
            /// All previous calls to `enter` must be valid.
            #[inline]
            unsafe fn wake_all(&mut self) {
                while let Some(head) = self.head {
                    // SAFETY: User-upheld invariant.
                    let node = unsafe { head.as_ref() };
                    // SAFETY: The access to the entire queue is exclusive.
                    unsafe {
                        self.head = *node.next.get();
                    }
                    node.status.store(Anchor::BUSY, Ordering::Relaxed);
                    node.handle.unpark();
                    node.status.store(Anchor::UNPARKED, Ordering::Release);
                }
            }
        }

        pub(crate) struct InnerRwLock {
            state: AtomicU32,
            queue: UnsafeCell<Queue>,
        }

        impl InnerRwLock {
            const QUEUE_STATE_MASK: u32 = 1;
            const LOCK_STATE_MASK: u32 = 1 << 1;
            const FIRST_COUNTER_MASK: u32 = {
                const FIRST_COUNTER_BITS: u32 = u32::BITS / 2 - 1;
                const FIRST_BIT: u32 = 1;
                let mut res = 0;
                let mut i = 0;
                while i < FIRST_COUNTER_BITS {
                    res <<= 1;
                    res += FIRST_BIT;
                    i += 1;
                }
                res << (Self::QUEUE_STATE_MASK.count_ones() + Self::LOCK_STATE_MASK.count_ones())
            };
            const SECOND_COUNTER_MASK: u32 =
                !0 & !Self::QUEUE_STATE_MASK & !Self::LOCK_STATE_MASK & !Self::FIRST_COUNTER_MASK;
            const LOCK_MASK: u32 = Self::LOCK_STATE_MASK | Self::FIRST_COUNTER_MASK | Self::SECOND_COUNTER_MASK;
            const FIRST_COUNTER_ONE: u32 = 1 << Self::FIRST_COUNTER_MASK.trailing_zeros();
            const SECOND_COUNTER_ONE: u32 = 1 << Self::SECOND_COUNTER_MASK.trailing_zeros();
            const QUEUE_AVAILABLE: u32 = Self::QUEUE_STATE_MASK;
            const QUEUE_BUSY: u32 = 0;
            const LOCK_MUTABLE: u32 = Self::LOCK_STATE_MASK;
            const LOCK_IMMUTABLE: u32 = 0;
            const EMPTY: u32 = 0;
            const GLOBAL_WRITER: u32 = Self::LOCK_MUTABLE;

            const fn new() -> Self {
                Self {
                    state: AtomicU32::new(Self::QUEUE_AVAILABLE | Self::EMPTY),
                    queue: UnsafeCell::new(Queue::new()),
                }
            }

            #[inline]
            fn wait(&self, loaded: &mut u32) {
                if *loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                    *loaded = self.state.load(Ordering::Relaxed);
                    hint::spin_loop();
                } else {
                    atomic::fence(Ordering::Acquire);
                    match self.state.compare_exchange_weak(
                        *loaded,
                        Self::QUEUE_BUSY | (*loaded & Self::LOCK_MASK),
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => {
                            let mut anchor = pin!(Anchor::new());
                            // SAFETY: - `state` provides synchronization - no other thread
                            //           can access the queue at this point.
                            //         - `anchor` calls `wait` once after this line.
                            unsafe {
                                (*self.queue.get()).enter(anchor.as_mut());
                            }
                            let anchor = anchor.into_ref();

                            while let Err(current) = self.state.compare_exchange_weak(
                                *loaded,
                                Self::QUEUE_AVAILABLE | (*loaded & Self::LOCK_MASK),
                                Ordering::Release,
                                Ordering::Relaxed,
                            ) {
                                *loaded = current;
                                hint::spin_loop();
                            }

                            // SAFETY: Turned the only mutable reference in form of
                            //         a `Pin<&mut Anchor>` into a `Pin<&Anchor>`.
                            unsafe { anchor.wait() }
                        }
                        Err(current) => {
                            *loaded = current;
                            hint::spin_loop();
                        }
                    }
                }
            }

            pub(crate) fn read(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_MASK == Self::GLOBAL_WRITER {
                        self.wait(&mut loaded);
                        loaded = self.state.load(Ordering::Relaxed);
                    } else if crate::inner::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
                        process::abort()
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the first counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::FIRST_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_read(&self) -> bool {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_MASK == Self::GLOBAL_WRITER {
                        return false;
                    } else if crate::inner::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
                        process::abort()
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the first counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::FIRST_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn read_all(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_STATE_MASK == Self::LOCK_MUTABLE {
                        self.wait(&mut loaded);
                        loaded = self.state.load(Ordering::Relaxed);
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort()
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_read_all(&self) -> bool {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_STATE_MASK == Self::LOCK_MUTABLE {
                        return false;
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort()
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn write(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_MASK == Self::GLOBAL_WRITER
                        || (loaded & Self::LOCK_STATE_MASK != Self::LOCK_MUTABLE
                            && loaded & Self::SECOND_COUNTER_MASK != 0)
                    {
                        self.wait(&mut loaded);
                        loaded = self.state.load(Ordering::Relaxed);
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort()
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            Self::LOCK_MUTABLE | unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_write(&self) -> bool {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_MASK == Self::GLOBAL_WRITER
                        || (loaded & Self::LOCK_STATE_MASK != Self::LOCK_MUTABLE
                            && loaded & Self::SECOND_COUNTER_MASK != 0)
                    {
                        return false;
                    } else if crate::inner::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
                        process::abort()
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: Checked above that the second counter can be safely incremented.
                            unsafe { loaded.unchecked_add(Self::SECOND_COUNTER_ONE) },
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn write_all(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_MASK != Self::EMPTY {
                        self.wait(&mut loaded);
                        loaded = self.state.load(Ordering::Relaxed);
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            (loaded & Self::QUEUE_STATE_MASK) | Self::GLOBAL_WRITER,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) fn try_write_all(&self) -> bool {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::LOCK_MASK != Self::EMPTY {
                        return false;
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            (loaded & Self::QUEUE_STATE_MASK) | Self::GLOBAL_WRITER,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
            }

            pub(crate) unsafe fn drop_reader_unchecked(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_ONE {
                        if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                            loaded = self.state.load(Ordering::Relaxed);
                            hint::spin_loop();
                        } else {
                            match self.state.compare_exchange_weak(
                                loaded,
                                Self::QUEUE_BUSY | (loaded & (Self::LOCK_STATE_MASK | Self::SECOND_COUNTER_MASK)),
                                Ordering::Acquire,
                                Ordering::Relaxed,
                            ) {
                                Ok(_) => break,
                                Err(current) => {
                                    loaded = current;
                                    hint::spin_loop();
                                }
                            }
                        }
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: User-upheld invariant.
                            unsafe { loaded.unchecked_sub(Self::FIRST_COUNTER_ONE) },
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
                // SAFETY: `state` provides synchronization - no other thread
                //         can access the queue at this point.
                unsafe { (*self.queue.get()).wake_one() };
                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }
            }

            pub(crate) unsafe fn drop_global_reader_unchecked(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_ONE {
                        if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                            loaded = self.state.load(Ordering::Relaxed);
                            hint::spin_loop();
                        } else {
                            match self.state.compare_exchange_weak(
                                loaded,
                                Self::QUEUE_BUSY | Self::LOCK_IMMUTABLE | (loaded & Self::FIRST_COUNTER_MASK),
                                Ordering::Acquire,
                                Ordering::Relaxed,
                            ) {
                                Ok(_) => break,
                                Err(current) => {
                                    loaded = current;
                                    hint::spin_loop();
                                }
                            }
                        }
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: User-upheld invariant.
                            unsafe { loaded.unchecked_sub(Self::SECOND_COUNTER_ONE) },
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
                // SAFETY: `state` provides synchronization - no other thread
                //         can access the queue at this point.
                unsafe { (*self.queue.get()).wake_all() };
                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }
            }

            pub(crate) unsafe fn drop_writer_unchecked(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_ONE {
                        if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                            loaded = self.state.load(Ordering::Relaxed);
                            hint::spin_loop();
                        } else {
                            match self.state.compare_exchange_weak(
                                loaded,
                                Self::QUEUE_BUSY | Self::LOCK_IMMUTABLE | (loaded & Self::FIRST_COUNTER_MASK),
                                Ordering::Acquire,
                                Ordering::Relaxed,
                            ) {
                                Ok(_) => break,
                                Err(current) => {
                                    loaded = current;
                                    hint::spin_loop();
                                }
                            }
                        }
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            // SAFETY: User-upheld invariant.
                            unsafe { loaded.unchecked_sub(Self::SECOND_COUNTER_ONE) },
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }
                // SAFETY: `state` provides synchronization - no other thread
                //         can access the queue at this point.
                unsafe { (*self.queue.get()).wake_all() };
                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }
            }

            pub(crate) unsafe fn drop_global_writer_unchecked(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_BUSY | Self::EMPTY,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }

                // SAFETY: `state` provides synchronization - no other thread
                //         can access the queue at this point.
                unsafe { (*self.queue.get()).wake_all() };
                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }
            }

            #[cfg(feature = "downgrade")]
            pub(crate) unsafe fn downgrade_writer_unchecked(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                loop {
                    if crate::inner::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
                        process::abort();
                    } else if loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_ONE {
                        if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                            loaded = self.state.load(Ordering::Relaxed);
                            hint::spin_loop();
                        } else {
                            match self.state.compare_exchange_weak(
                                loaded,
                                Self::QUEUE_BUSY
                                    | Self::LOCK_IMMUTABLE
                                    // SAFETY: Checked above that the first counter can be safely incremented.
                                    | (unsafe { loaded.unchecked_add(Self::FIRST_COUNTER_ONE) }
                                        & Self::FIRST_COUNTER_MASK),
                                Ordering::Acquire,
                                Ordering::Relaxed,
                            ) {
                                Ok(_) => break,
                                Err(current) => {
                                    loaded = current;
                                    hint::spin_loop();
                                }
                            }
                        }
                    } else {
                        match self.state.compare_exchange_weak(
                            loaded,
                            unsafe {
                                loaded
                                    // SAFETY: User-upheld invariant.
                                    .unchecked_sub(Self::SECOND_COUNTER_ONE)
                                    // SAFETY: Checked above that the first counter can be safely incremented.
                                    .unchecked_add(Self::FIRST_COUNTER_ONE)
                            },
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return,
                            Err(current) => {
                                loaded = current;
                                hint::spin_loop();
                            }
                        }
                    }
                }

                // SAFETY: `state` provides synchronization - no other thread
                //         can access the queue at this point.
                unsafe { (*self.queue.get()).wake_all() };
                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }
            }

            #[cfg(feature = "downgrade")]
            pub(crate) unsafe fn downgrade_global_writer_unchecked(&self) {
                let mut loaded = self.state.load(Ordering::Relaxed);
                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_BUSY | Self::SECOND_COUNTER_ONE,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }

                // SAFETY: `state` provides synchronization - no other thread
                //         can access the queue at this point.
                unsafe { (*self.queue.get()).wake_all() };

                while let Err(current) = self.state.compare_exchange_weak(
                    loaded,
                    Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    loaded = current;
                    hint::spin_loop();
                }
            }
        }

        unsafe impl Sync for InnerRwLock {}

        #[cfg(test)]
        mod tests {
            use super::InnerRwLock;
            use std::{hint, num::NonZeroU16, sync::atomic::Ordering};

            const ONE: NonZeroU16 = NonZeroU16::new(1).unwrap();
            const TWO: NonZeroU16 = NonZeroU16::new(2).unwrap();

            #[derive(Debug)]
            pub(crate) enum LockState {
                Empty,
                Readers(NonZeroU16),
                GlobalReaders(NonZeroU16),
                Writers(NonZeroU16),
                GlobalWriter,
                ReadersAndGlobalReaders {
                    readers: NonZeroU16,
                    global_readers: NonZeroU16,
                },
                ReadersAndWriters {
                    readers: NonZeroU16,
                    writers: NonZeroU16,
                },
            }

            impl InnerRwLock {
                pub(crate) fn state(&self) -> LockState {
                    let loaded = self.state.load(Ordering::Relaxed);
                    let first_counter = NonZeroU16::new(
                        ((loaded & Self::FIRST_COUNTER_MASK) >> Self::FIRST_COUNTER_MASK.trailing_zeros()) as _,
                    );
                    let second_counter = NonZeroU16::new(
                        ((loaded & Self::SECOND_COUNTER_MASK) >> Self::SECOND_COUNTER_MASK.trailing_zeros()) as _,
                    );
                    match (
                        loaded & Self::LOCK_STATE_MASK == Self::LOCK_MUTABLE,
                        first_counter,
                        second_counter,
                    ) {
                        (false, None, None) => LockState::Empty,
                        (false, Some(readers), None) => LockState::Readers(readers),
                        (false, None, Some(global_readers)) => LockState::GlobalReaders(global_readers),
                        (true, None, Some(writers)) => LockState::Writers(writers),
                        (true, None, None) => LockState::GlobalWriter,
                        (false, Some(readers), Some(global_readers)) => LockState::ReadersAndGlobalReaders {
                            readers,
                            global_readers,
                        },
                        (true, Some(readers), Some(writers)) => LockState::ReadersAndWriters { readers, writers },
                        (true, Some(_), None) => unsafe { hint::unreachable_unchecked() },
                    }
                }
            }

            mod single_threaded {
                use super::{super::InnerRwLock, LockState, ONE, TWO};
                use std::assert_matches::assert_matches;

                #[test]
                fn read() {
                    let lock = InnerRwLock::new();

                    lock.read();
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.read();

                    assert!(lock.try_read());
                    assert_matches!(lock.state(), LockState::Readers(TWO));

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    lock.read_all();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndGlobalReaders {
                            readers: ONE,
                            global_readers: ONE
                        }
                    );
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    lock.write();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndWriters {
                            readers: ONE,
                            writers: ONE
                        }
                    );
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::Readers(ONE));
                }

                #[test]
                fn read_all() {
                    let lock = InnerRwLock::new();

                    lock.read_all();
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.read_all();

                    assert!(lock.try_read_all());
                    assert_matches!(lock.state(), LockState::GlobalReaders(TWO));

                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    lock.read();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndGlobalReaders {
                            readers: ONE,
                            global_readers: ONE
                        }
                    );

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    assert!(!lock.try_write());
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                }

                #[test]
                fn write() {
                    let lock = InnerRwLock::new();

                    lock.write();
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.write();

                    assert!(lock.try_write());
                    assert_matches!(lock.state(), LockState::Writers(TWO));

                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    lock.read();
                    assert_matches!(
                        lock.state(),
                        LockState::ReadersAndWriters {
                            readers: ONE,
                            writers: ONE
                        }
                    );

                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    assert!(!lock.try_read_all());
                    assert_matches!(lock.state(), LockState::Writers(ONE));

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::Writers(ONE));
                }

                #[test]
                fn write_all() {
                    let lock = InnerRwLock::new();

                    lock.write_all();
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    unsafe {
                        lock.drop_global_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Empty);

                    lock.write_all();

                    assert!(!lock.try_read());
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    assert!(!lock.try_read_all());
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    assert!(!lock.try_write());
                    assert_matches!(lock.state(), LockState::GlobalWriter);

                    assert!(!lock.try_write_all());
                    assert_matches!(lock.state(), LockState::GlobalWriter);
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_writer() {
                    let lock = InnerRwLock::new();
                    lock.write();

                    unsafe {
                        lock.downgrade_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(ONE));

                    lock.write();
                    unsafe {
                        lock.downgrade_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::Readers(TWO));
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_global_writer() {
                    let lock = InnerRwLock::new();
                    lock.write_all();

                    unsafe {
                        lock.downgrade_global_writer_unchecked();
                    }
                    assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                }
            }

            mod concurrent {
                use super::{super::InnerRwLock, LockState, ONE, TWO};
                use std::{assert_matches::assert_matches, sync::Barrier, thread};

                #[test]
                fn read() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ...0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::Readers(ONE));

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::Readers(TWO));

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndGlobalReaders {
                                    readers: ONE,
                                    global_readers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_global_reader_unchecked();
                            }
                            barrier.wait();
                            // ...6
                            barrier.wait();
                            // 7
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndWriters {
                                    readers: ONE,
                                    writers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_writer_unchecked();
                            }
                            barrier.wait();
                            // ...8
                            barrier.wait();
                            // 9
                            assert_matches!(lock.state(), LockState::Readers(ONE));
                        });

                        // 0
                        lock.read();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.read();

                        assert!(lock.try_read());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::Readers(ONE));

                        lock.read_all();
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::Readers(ONE));

                        lock.write();
                        barrier.wait();
                        // ...7
                        barrier.wait();
                        // 8
                        assert_matches!(lock.state(), LockState::Readers(ONE));

                        assert!(!lock.try_write_all());
                        barrier.wait();
                    })
                }

                #[test]
                fn read_all() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ..0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                            unsafe {
                                lock.drop_global_reader_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::GlobalReaders(TWO));

                            unsafe {
                                lock.drop_global_reader_unchecked();
                            }
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndGlobalReaders {
                                    readers: ONE,
                                    global_readers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...6
                            barrier.wait();
                            // 7
                            assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                            assert!(!lock.try_write_all());
                            barrier.wait();
                        });

                        // 0
                        lock.read_all();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.read_all();

                        assert!(lock.try_read_all());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                        lock.read();
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::GlobalReaders(ONE));

                        assert!(!lock.try_write());
                        barrier.wait();
                        // ...7
                        barrier.wait();
                        // 8
                        assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                    });
                }

                #[test]
                fn write() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ..0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::Writers(ONE));

                            unsafe {
                                lock.drop_writer_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::Writers(TWO));

                            unsafe {
                                lock.drop_writer_unchecked();
                            }
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(
                                lock.state(),
                                LockState::ReadersAndWriters {
                                    readers: ONE,
                                    writers: ONE
                                }
                            );

                            unsafe {
                                lock.drop_reader_unchecked();
                            }
                            barrier.wait();
                            // ...6
                            barrier.wait();
                            // 7
                            assert_matches!(lock.state(), LockState::Writers(ONE));

                            assert!(!lock.try_write_all());
                            barrier.wait();
                        });

                        // 0
                        lock.write();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.write();

                        assert!(lock.try_write());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::Writers(ONE));

                        lock.read();
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::Writers(ONE));

                        assert!(!lock.try_read_all());
                        barrier.wait();
                        // ...7
                        barrier.wait();
                        // 8
                        assert_matches!(lock.state(), LockState::Writers(ONE));
                    });
                }

                #[test]
                fn write_all() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ..0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::GlobalWriter);

                            unsafe {
                                lock.drop_global_writer_unchecked();
                            }
                            barrier.wait();
                            // ...2
                            barrier.wait();
                            // 3
                            assert_matches!(lock.state(), LockState::GlobalWriter);

                            assert!(!lock.try_read_all());
                            barrier.wait();
                            // ...4
                            barrier.wait();
                            // 5
                            assert_matches!(lock.state(), LockState::GlobalWriter);

                            assert!(!lock.try_write_all());
                            barrier.wait();
                        });

                        // 0
                        lock.write_all();
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Empty);

                        lock.write_all();

                        assert!(!lock.try_read());
                        barrier.wait();
                        // ...3
                        barrier.wait();
                        // 4
                        assert_matches!(lock.state(), LockState::GlobalWriter);

                        assert!(!lock.try_write());
                        barrier.wait();
                        // ...5
                        barrier.wait();
                        // 6
                        assert_matches!(lock.state(), LockState::GlobalWriter);
                    });
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_writer() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ...0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::Readers(ONE));

                            lock.write();
                            unsafe {
                                lock.downgrade_writer_unchecked();
                            }
                            barrier.wait();
                        });

                        // 0
                        lock.write();

                        unsafe {
                            lock.downgrade_writer_unchecked();
                        }
                        barrier.wait();
                        // ...1
                        barrier.wait();
                        // 2
                        assert_matches!(lock.state(), LockState::Readers(TWO));
                    })
                }

                #[cfg(feature = "downgrade")]
                #[test]
                fn downgrade_global_writer() {
                    let lock = InnerRwLock::new();
                    let barrier = Barrier::new(2);

                    thread::scope(|s| {
                        s.spawn(|| {
                            // ...0
                            barrier.wait();
                            // 1
                            assert_matches!(lock.state(), LockState::GlobalReaders(ONE));
                        });

                        // 0
                        lock.write_all();

                        unsafe {
                            lock.downgrade_global_writer_unchecked();
                        }
                        barrier.wait();
                    });
                }
            }
        }
    }
}
