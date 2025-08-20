use std::{
    hint, process,
    sync::atomic::{AtomicU32, Ordering},
};

pub(crate) struct InnerSliceRwLock(AtomicU32);

impl InnerSliceRwLock {
    const STATE_MASK: u32 = 1;
    const COUNTER_ONE: u32 = 1 << Self::STATE_MASK.count_ones();
    const WRITERS_STATE: u32 = 0;
    const SLICE_READERS_STATE: u32 = 1;
    const EMPTY: u32 = 0;
    const SLICE_WRITER: u32 = 1;
    pub(crate) const GUARDS_COUNT_MAX: u32 = u32::MAX >> Self::STATE_MASK.count_ones();

    pub(crate) const fn new() -> Self {
        Self(AtomicU32::new(Self::EMPTY))
    }

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
            } else if loaded & Self::STATE_MASK == Self::WRITERS_STATE {
                let counter = loaded >> Self::STATE_MASK.count_ones();
                if super::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                    process::abort();
                }
                match self.0.compare_exchange_weak(
                    loaded,
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
            } else if loaded & Self::STATE_MASK == Self::WRITERS_STATE {
                let counter = loaded >> Self::STATE_MASK.count_ones();
                if super::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                    process::abort()
                }
                match self.0.compare_exchange_weak(
                    loaded,
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

    pub(crate) fn read_slice(&self) {
        let mut loaded = self.0.load(Ordering::Relaxed);
        loop {
            if loaded == Self::EMPTY {
                match self.0.compare_exchange_weak(
                    Self::EMPTY,
                    Self::SLICE_READERS_STATE | Self::COUNTER_ONE,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(current) => {
                        loaded = current;
                        hint::spin_loop();
                    }
                }
            } else if loaded & Self::STATE_MASK == Self::SLICE_READERS_STATE {
                let counter = loaded >> Self::STATE_MASK.count_ones();
                if super::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                    process::abort();
                }
                match self.0.compare_exchange_weak(
                    loaded,
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

    pub(crate) fn try_read_slice(&self) -> bool {
        let mut loaded = self.0.load(Ordering::Relaxed);
        loop {
            if loaded == Self::EMPTY {
                match self.0.compare_exchange_weak(
                    Self::EMPTY,
                    Self::SLICE_READERS_STATE | Self::COUNTER_ONE,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(current) => {
                        loaded = current;
                        hint::spin_loop();
                    }
                }
            } else if loaded & Self::STATE_MASK == Self::SLICE_READERS_STATE {
                let counter = loaded >> Self::STATE_MASK.count_ones();
                if super::unlikely(counter == Self::GUARDS_COUNT_MAX) {
                    process::abort();
                }
                match self.0.compare_exchange_weak(
                    loaded,
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

    pub(crate) fn write_slice(&self) {
        let mut loaded = self.0.load(Ordering::Relaxed);
        loop {
            if loaded == Self::EMPTY {
                match self.0.compare_exchange_weak(
                    Self::EMPTY,
                    Self::SLICE_WRITER,
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

    pub(crate) fn try_write_slice(&self) -> bool {
        let mut loaded = self.0.load(Ordering::Relaxed);
        loop {
            if loaded == Self::EMPTY {
                match self.0.compare_exchange_weak(
                    Self::EMPTY,
                    Self::SLICE_WRITER,
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

    pub(crate) unsafe fn drop_writer_unchecked(&self) {
        let mut loaded = self.0.load(Ordering::Relaxed);
        loop {
            let counter = loaded >> Self::STATE_MASK.count_ones();
            match self.0.compare_exchange_weak(
                loaded,
                if counter == 0 {
                    unsafe { hint::unreachable_unchecked() }
                } else if counter == 1 {
                    Self::EMPTY
                } else {
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

    pub(crate) unsafe fn drop_slice_reader_unchecked(&self) {
        let mut loaded = self.0.load(Ordering::Relaxed);
        loop {
            let counter = loaded >> Self::STATE_MASK.count_ones();
            match self.0.compare_exchange_weak(
                loaded,
                if counter == 0 {
                    unsafe { hint::unreachable_unchecked() }
                } else if counter == 1 {
                    Self::EMPTY
                } else {
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

    pub(crate) unsafe fn drop_slice_writer_unchecked(&self) {
        self.0.store(Self::EMPTY, Ordering::Release);
        atomic_wait::wake_all(&self.0);
    }
}

pub(crate) struct LockState(AtomicU32);

impl LockState {
    const POISONED: u32 = 1;
    const COUNTER_ONE: u32 = 1;
    pub const MAX_COUNT: u32 = u32::MAX >> Self::POISONED.count_ones();

    #[inline]
    const fn new() -> Self {
        Self(AtomicU32::new(0))
    }

    #[inline]
    pub(crate) fn is_poisoned(&self) -> bool {
        self.0.load(Ordering::Relaxed) & Self::POISONED != 0
    }

    #[inline]
    pub(crate) fn clear_poison(&self) {
        self.0.fetch_and(!Self::POISONED, Ordering::Relaxed);
    }

    #[inline]
    pub(crate) fn poison(&self) {
        self.0.fetch_or(Self::POISONED, Ordering::Relaxed);
    }

    #[inline]
    pub(crate) fn get_counter(&self) -> u32 {
        self.0.load(Ordering::Relaxed) >> Self::POISONED.count_ones()
    }

    pub(crate) unsafe fn fetch_increment_counter_unchecked(&self, order: Ordering) -> u32 {
        self.0.fetch_add(Self::COUNTER_ONE, order) >> Self::POISONED.count_ones()
    }

    #[inline]
    pub(crate) unsafe fn fetch_decrement_counter_unchecked(&self, order: Ordering) -> u32 {
        self.0.fetch_sub(Self::COUNTER_ONE, order) >> Self::POISONED.count_ones()
    }
}

pub(crate) struct Metadata {
    pub(crate) lock: InnerSliceRwLock,
    pub(crate) state: LockState,
}

impl Metadata {
    pub(crate) fn new() -> Self {
        Self {
            lock: InnerSliceRwLock::new(),
            state: LockState::new(),
        }
    }
}

pub(crate) mod alloc {
    use crate::inner::{InnerSliceRwLock, LockState, Metadata};
    use std::{
        alloc::{AllocError, Allocator, Global, Layout, LayoutError, handle_alloc_error},
        mem::MaybeUninit,
        ptr::{self, NonNull},
    };

    #[repr(C)]
    pub(crate) struct Allocation<T, A: Allocator = Global> {
        allocator: A,
        pub(crate) metadata: Metadata,
        pub(crate) slice: [T],
    }

    impl<T, A: Allocator> Allocation<T, A> {
        /// Returns the layout that describes an `Allocation<T, A>`
        const fn get_layout(len: usize) -> Result<Layout, LayoutError> {
            match Layout::new::<A>().extend(
                match Layout::new::<Metadata>().extend(
                    match Layout::array::<T>(len) {
                        Ok(array_layout) => array_layout,
                        Err(err) => return Err(err),
                    }
                    .pad_to_align(),
                ) {
                    Ok((layout, _)) => layout,
                    Err(err) => return Err(err),
                },
            ) {
                Ok((layout, _)) => Ok(layout),
                Err(err) => Err(err),
            }
        }

        /// Deallocates the memory referenced by `ptr`.
        /// 
        /// # Safety
        /// See `alloc::Allocator::deallocate`
        pub(crate) unsafe fn deallocate(ptr: NonNull<Self>) {
            unsafe {
                let layout = Layout::for_value(&*ptr.as_ptr());
                let allocator = (&raw mut (*ptr.as_ptr()).allocator).read();
                (&raw mut (*ptr.as_ptr()).metadata).drop_in_place();
                (&raw mut (*ptr.as_ptr()).slice).drop_in_place();
                allocator.deallocate(ptr.cast(), layout);
            }
        }

        /// Returns a reference to the metadata of the `Allocation` referenced by `ptr`
        /// without constructing a reference to the whole object.
        /// 
        /// # Safety
        /// `ptr` must point to a valid instance of `Self` that outlives `'a`.
        #[inline]
        pub(crate) const unsafe fn get_metadata_disjoint<'a>(ptr: NonNull<Self>) -> &'a Metadata {
            unsafe { &(*ptr.as_ptr()).metadata }
        }

        /// Returns a mutable reference to the whole slice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object
        /// 
        /// # Safety
        /// * `ptr` must point to a valid instance of `Self` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_slice_mut_disjoint<'a>(ptr: NonNull<Self>) -> &'a mut [T] {
            unsafe { &mut (*ptr.as_ptr()).slice }
        }

        /// Returns a mutable reference to an element of the slice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object
        /// 
        /// # Safety
        /// * `ptr` must point to a valid instance of `Self` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        #[inline]
        pub(crate) const unsafe fn get_elem_mut_disjoint<'a>(ptr: NonNull<Self>, idx: usize) -> &'a mut T {
            unsafe { &mut *(&raw mut (*ptr.as_ptr()).slice).cast::<T>().add(idx) }
        }

        /// Returns a mutable reference to a subslice of the `Allocation` referenced by `ptr`
        /// without constructing a (mutable) reference to the whole object
        /// 
        /// # Safety
        /// * `ptr` must point to a valid instance of `Self` that outlives `'a`.
        /// * The returned reference must not violate aliasing rules.
        pub(crate) const unsafe fn get_subslice_mut_disjoint<'a>(
            ptr: NonNull<Self>,
            start: usize,
            len: usize,
        ) -> &'a mut [T] {
            unsafe { &mut *ptr::from_raw_parts_mut((&raw mut (*ptr.as_ptr()).slice).cast::<T>().add(start), len) }
        }
    }

    impl<T, A: Allocator> Allocation<MaybeUninit<T>, A> {
        /// Allocates an instance of an `Allocation` with uninitialized contents in the provided allocator
        pub(crate) fn allocate_uninit_in(len: usize, allocator: A) -> NonNull<Self> {
            let layout = Self::get_layout(len).unwrap();
            let ptr = NonNull::<Self>::from_raw_parts(
                allocator
                    .allocate(layout)
                    .unwrap_or_else(|_| handle_alloc_error(layout))
                    .cast::<()>(),
                len,
            );
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it
            unsafe {
                (&raw mut (*ptr.as_ptr()).allocator).write(allocator);
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata {
                    lock: InnerSliceRwLock::new(),
                    state: LockState::new(),
                });
            }
            ptr
        }

        /// Allocates an instance of an `Allocation` with uninitialized contents in the provided allocator,
        /// returning an error if the allocation fails
        pub(crate) fn try_allocate_uninit_in(len: usize, allocator: A) -> Result<NonNull<Self>, AllocError> {
            let layout = match Self::get_layout(len) {
                Ok(layout) => layout,
                Err(_) => return Err(AllocError),
            };
            let ptr = NonNull::<Self>::from_raw_parts(allocator.allocate(layout)?.cast::<()>(), len);
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it
            unsafe {
                (&raw mut (*ptr.as_ptr()).allocator).write(allocator);
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata {
                    lock: InnerSliceRwLock::new(),
                    state: LockState::new(),
                });
            }
            Ok(ptr)
        }

        /// Allocates an instance of an `Allocation` with uninitialized contents,
        /// with the `slice` field being filled with `0` bytes in the provided allocator
        pub(crate) fn allocate_zeroed_in(len: usize, allocator: A) -> NonNull<Self> {
            let layout = Self::get_layout(len).unwrap();
            let ptr = NonNull::<Self>::from_raw_parts(
                allocator
                    .allocate_zeroed(layout)
                    .unwrap_or_else(|_| handle_alloc_error(layout))
                    .cast::<()>(),
                len,
            );
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it
            unsafe {
                (&raw mut (*ptr.as_ptr()).allocator).write(allocator);
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata {
                    lock: InnerSliceRwLock::new(),
                    state: LockState::new(),
                });
            }
            ptr
        }

        /// Allocates an instance of an `Allocation` with uninitialized contents,
        /// with the `slice` field being filled with `0` bytes in the provided allocator,
        /// returning an error if allocation fails
        pub(crate) fn try_allocate_zeroed_in(len: usize, allocator: A) -> Result<NonNull<Self>, AllocError> {
            let layout = match Self::get_layout(len) {
                Ok(layout) => layout,
                Err(_) => return Err(AllocError),
            };
            let ptr = NonNull::<Self>::from_raw_parts(allocator.allocate_zeroed(layout)?.cast::<()>(), len);
            // SAFETY: `ptr` points to a valid allocation and has exclusive access to it
            unsafe {
                (&raw mut (*ptr.as_ptr()).allocator).write(allocator);
                (&raw mut (*ptr.as_ptr()).metadata).write(Metadata {
                    lock: InnerSliceRwLock::new(),
                    state: LockState::new(),
                });
            }
            Ok(ptr)
        }
    }
}
