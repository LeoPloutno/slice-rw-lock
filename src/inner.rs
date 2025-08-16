use std::{
    alloc::{self, Layout, LayoutError},
    hint,
    mem::MaybeUninit,
    process,
    ptr::{self, NonNull},
    sync::atomic::{AtomicU32, Ordering},
};

pub(super) struct InnerSliceRwLock(AtomicU32);

impl InnerSliceRwLock {
    const STATE_MASK: u32 = 1;
    const COUNTER_ONE: u32 = 1 << Self::STATE_MASK.count_ones();
    const WRITERS_STATE: u32 = 0;
    const SLICE_READERS_STATE: u32 = 1;
    const EMPTY: u32 = 0;
    const SLICE_WRITER: u32 = 1;
    pub(super) const GUARDS_COUNT_MAX: u32 = u32::MAX >> Self::STATE_MASK.count_ones();

    pub(super) const fn new() -> Self {
        Self(AtomicU32::new(Self::EMPTY))
    }

    pub(super) fn write(&self) {
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

    pub(super) fn try_write(&self) -> bool {
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

    pub(super) fn read_slice(&self) {
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

    pub(super) fn try_read_slice(&self) -> bool {
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

    pub(super) fn write_slice(&self) {
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

    pub(super) fn try_write_slice(&self) -> bool {
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

    pub(super) unsafe fn drop_writer_unchecked(&self) {
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

    pub(super) unsafe fn drop_slice_reader_unchecked(&self) {
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

    pub(super) unsafe fn drop_slice_writer_unchecked(&self) {
        self.0.store(Self::EMPTY, Ordering::Release);
        atomic_wait::wake_all(&self.0);
    }
}

pub(super) struct LockState(AtomicU32);

impl LockState {
    const POISONED: u32 = 1;
    const COUNTER_ONE: u32 = 1;
    pub const MAX_COUNT: u32 = u32::MAX >> Self::POISONED.count_ones();

    #[inline]
    const fn new() -> Self {
        Self(AtomicU32::new(0))
    }

    #[inline]
    pub(super) fn is_poisoned(&self) -> bool {
        self.0.load(Ordering::Relaxed) & Self::POISONED != 0
    }

    #[inline]
    pub(super) fn clear_poison(&self) {
        self.0.fetch_and(!Self::POISONED, Ordering::Relaxed);
    }

    #[inline]
    pub(super) fn poison(&self) {
        self.0.fetch_or(Self::POISONED, Ordering::Relaxed);
    }

    #[inline]
    pub(super) fn get_counter(&self) -> u32 {
        self.0.load(Ordering::Relaxed) >> Self::POISONED.count_ones()
    }

    pub(super) unsafe fn fetch_increment_counter_unchecked(&self, order: Ordering) -> u32 {
        self.0.fetch_add(Self::COUNTER_ONE, order) >> Self::POISONED.count_ones()
    }

    #[inline]
    pub(super) unsafe fn fetch_decrement_counter_unchecked(&self, order: Ordering) -> u32 {
        self.0.fetch_sub(Self::COUNTER_ONE, order) >> Self::POISONED.count_ones()
    }
}

pub(super) struct AllocatedMetadata {
    pub(super) lock: InnerSliceRwLock,
    pub(super) state: LockState,
}

#[repr(C)]
pub(super) struct Allocation<T> {
    pub(super) metadata: AllocatedMetadata,
    pub(super) slice: [T],
}

impl<T> Allocation<T> {
    const fn get_layout(len: usize) -> Result<Layout, LayoutError> {
        match Layout::new::<AllocatedMetadata>().extend(
            match Layout::array::<T>(len) {
                Ok(array_layout) => array_layout,
                Err(err) => return Err(err),
            }
            .pad_to_align(),
        ) {
            Ok((layout, _)) => Ok(layout),
            Err(err) => Err(err),
        }
    }

    pub(super) unsafe fn realloc(ptr: NonNull<[T]>) -> NonNull<Self> {
        let len = ptr::metadata(ptr.as_ptr());
        let layout = Self::get_layout(len).unwrap();
        let new = NonNull::<Self>::from_raw_parts(NonNull::new(unsafe { alloc::alloc(layout) }).unwrap_or_else(|| alloc::handle_alloc_error(layout)), len);
        unsafe {
            // Copy original data into newly allocated memory and deallocate it
            (&raw mut (*new.as_ptr()).slice).cast::<T>().copy_from_nonoverlapping(ptr.as_ptr().cast::<T>(), len);
            alloc::dealloc(ptr.as_ptr().cast(), Layout::array::<T>(len).unwrap());

            // Initialize metadata
            (&raw mut (*new.as_ptr()).metadata).write(AllocatedMetadata {
                lock: InnerSliceRwLock::new(),
                state: LockState::new(),
            });
        }
        new

    }

    pub(super) unsafe fn dealloc(ptr: NonNull<Self>) {
        unsafe {
            ptr.drop_in_place();
            alloc::dealloc(
                ptr.as_ptr().cast(),
                Self::get_layout(ptr::metadata(ptr.as_ptr())).unwrap(),
            );
        }
    }

    #[inline]
    pub(super) const unsafe fn get_metadata_disjoint<'a>(ptr: NonNull<Self>) -> &'a AllocatedMetadata {
        unsafe { &(*ptr.as_ptr()).metadata }
    }

    #[inline]
    pub(super) const unsafe fn get_slice_mut_disjoint<'a>(ptr: NonNull<Self>) -> &'a mut [T] {
        unsafe { &mut (*ptr.as_ptr()).slice }
    }

    #[inline]
    pub(super) const unsafe fn get_elem_mut_disjoint<'a>(ptr: NonNull<Self>, idx: usize) -> &'a mut T {
        unsafe { &mut *(&raw mut (*ptr.as_ptr()).slice).cast::<T>().add(idx) }
    }

    pub(super) const unsafe fn get_subslice_mut_disjoint<'a>(ptr: NonNull<Self>, start: usize, len: usize) -> &'a mut [T] {
        unsafe { &mut *ptr::from_raw_parts_mut((&raw mut (*ptr.as_ptr()).slice).cast::<T>().add(start), len) }
    }
}

impl<T> Allocation<MaybeUninit<T>> {
    pub(super) unsafe fn alloc_uninit(len: usize) -> NonNull<Self> {
        let layout = Self::get_layout(len).unwrap();
        let ptr = NonNull::<Self>::from_raw_parts(
            NonNull::new(unsafe { alloc::alloc(layout) }).unwrap_or_else(|| alloc::handle_alloc_error(layout)),
            len,
        );
        unsafe {
            // Initialize metadata
            (&raw mut (*ptr.as_ptr()).metadata).write(AllocatedMetadata {
                lock: InnerSliceRwLock::new(),
                state: LockState::new(),
            });
        }
        ptr
    }

    pub(super) unsafe fn alloc_zeroed(len: usize) -> NonNull<Self> {
        let layout = Self::get_layout(len).unwrap();
        let ptr = NonNull::<Self>::from_raw_parts(
            NonNull::new(unsafe { alloc::alloc_zeroed(layout) }).unwrap_or_else(|| alloc::handle_alloc_error(layout)),
            len,
        );
        unsafe {
            (&raw mut (*ptr.as_ptr()).metadata).write(AllocatedMetadata {
                lock: InnerSliceRwLock::new(),
                state: LockState::new(),
            });
        }
        ptr
    }
}
