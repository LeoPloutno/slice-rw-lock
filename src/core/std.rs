use crate::core;
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
    handle: Thread,
    state: AtomicU8,
    phantom: PhantomPinned,
}

impl Anchor {
    const PARKED: u8 = 0;
    const BUSY: u8 = 1;
    const UNPARKED: u8 = 2;

    // Creates a new anchor to the current thread, initialized to `PARKEDS` state.
    pub(super) fn new() -> Self {
        Self {
            next: const { UnsafeCell::new(None) },
            handle: thread::current(),
            state: const { AtomicU8::new(Self::PARKED) },
            phantom: PhantomPinned,
        }
    }

    /// Wait until another thread wakes this one up.
    ///
    /// # Safety
    ///
    /// There must not exist any mutable references to the anchor at this point.
    unsafe fn wait(self: &Pin<&Self>) {
        //self.status.store(Self::PARKED, Ordering::Relaxed);
        while self.state.load(Ordering::Relaxed) == Self::PARKED {
            thread::park();
        }
        //atomic::fence(Ordering::Acquire);
        while self.state.load(Ordering::Relaxed) != Self::UNPARKED {
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
    const unsafe fn enter<'a, 'b>(&'a mut self, anchor: Pin<&'b mut Anchor>) -> Pin<&'b Anchor> {
        // SAFETY: Nothing is moved out of `anchor` throughout this function.
        let anchor = anchor.into_ref();
        match self {
            matched @ &mut Queue { head: None, .. } => {
                let node = Some(NonNull::from_ref(anchor.get_ref()));
                matched.head = node;
                matched.tail = node;
            }
            Queue {
                head: Some(_),
                tail: Some(tail),
            } => {
                let node_non_null = NonNull::from_ref(anchor.get_ref());
                // SAFETY: The access to the entire queue is exclusive.
                unsafe {
                    *tail.as_ref().next.get() = Some(node_non_null);
                }
                *tail = node_non_null;
            }
            // SAFETY: By construction, if `head` is non-null, so is `tail`.
            _ => unsafe { hint::unreachable_unchecked() },
        }
        anchor
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
            node.state.store(Anchor::BUSY, Ordering::Release);
            node.handle.unpark();
            node.state.store(Anchor::UNPARKED, Ordering::Release);
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
            node.state.store(Anchor::BUSY, Ordering::Release);
            node.handle.unpark();
            node.state.store(Anchor::UNPARKED, Ordering::Release);
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
    const SECOND_COUNTER_MASK: u32 = !0 & !Self::QUEUE_STATE_MASK & !Self::LOCK_STATE_MASK & !Self::FIRST_COUNTER_MASK;
    const LOCK_MASK: u32 = Self::LOCK_STATE_MASK | Self::FIRST_COUNTER_MASK | Self::SECOND_COUNTER_MASK;
    const FIRST_COUNTER_ONE: u32 = 1 << Self::FIRST_COUNTER_MASK.trailing_zeros();
    const SECOND_COUNTER_ONE: u32 = 1 << Self::SECOND_COUNTER_MASK.trailing_zeros();
    const QUEUE_AVAILABLE: u32 = Self::QUEUE_STATE_MASK;
    const QUEUE_BUSY: u32 = 0;
    const LOCK_MUTABLE: u32 = Self::LOCK_STATE_MASK;
    const LOCK_IMMUTABLE: u32 = 0;
    const LOCK_UNLOCKED: u32 = 0;
    const LOCK_GLOBAL_WRITER: u32 = Self::LOCK_MUTABLE;

    pub(crate) const fn new() -> Self {
        Self {
            state: AtomicU32::new(Self::QUEUE_AVAILABLE | Self::LOCK_UNLOCKED),
            queue: UnsafeCell::new(Queue::new()),
        }
    }

    #[inline]
    fn wait(&self, loaded: &mut u32) {
        let anchor = pin!(Anchor::new());
        // SAFETY: - `state` provides synchronization - no other thread
        //           can access the queue at this point.
        //         - `anchor` calls `wait` once after this line.
        let anchor = unsafe { (*self.queue.get()).enter(anchor) };

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
        unsafe {
            anchor.wait();
        }
    }

    pub(crate) fn read(&self) {
        let mut loaded = self.state.load(Ordering::Relaxed);
        loop {
            if loaded & Self::LOCK_MASK == Self::LOCK_GLOBAL_WRITER {
                if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                    loaded = self.state.load(Ordering::Relaxed);
                    hint::spin_loop();
                } else {
                    atomic::fence(Ordering::Acquire);
                    match self
                        .state
                        .compare_exchange_weak(loaded, Self::QUEUE_BUSY | (loaded & Self::LOCK_MASK), Ordering::Acquire, Ordering::Relaxed)
                    {
                        Ok(_) => {
                            self.wait(&mut loaded);
                            loaded = self.state.load(Ordering::Relaxed);
                        }
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                }
            } else if core::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
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
            if loaded & Self::LOCK_MASK == Self::LOCK_GLOBAL_WRITER {
                return false;
            } else if core::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
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
                if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                    loaded = self.state.load(Ordering::Relaxed);
                    hint::spin_loop();
                } else {
                    atomic::fence(Ordering::Acquire);
                    match self
                        .state
                        .compare_exchange_weak(loaded, Self::QUEUE_BUSY | (loaded & Self::LOCK_MASK), Ordering::Acquire, Ordering::Relaxed)
                    {
                        Ok(_) => {
                            self.wait(&mut loaded);
                            loaded = self.state.load(Ordering::Relaxed);
                        }
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                }
            } else if core::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
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
            } else if core::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
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
            if loaded & Self::LOCK_MASK == Self::LOCK_GLOBAL_WRITER
                || (loaded & Self::LOCK_STATE_MASK != Self::LOCK_MUTABLE && loaded & Self::SECOND_COUNTER_MASK != 0)
            // !
            {
                if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                    loaded = self.state.load(Ordering::Relaxed);
                    hint::spin_loop();
                } else {
                    atomic::fence(Ordering::Acquire);
                    match self
                        .state
                        .compare_exchange_weak(loaded, Self::QUEUE_BUSY | (loaded & Self::LOCK_MASK), Ordering::Acquire, Ordering::Relaxed)
                    {
                        Ok(_) => {
                            self.wait(&mut loaded);
                            loaded = self.state.load(Ordering::Relaxed);
                        }
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                }
            } else if core::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
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
            if loaded & Self::LOCK_MASK == Self::LOCK_GLOBAL_WRITER
                || (loaded & Self::LOCK_STATE_MASK != Self::LOCK_MUTABLE && loaded & Self::SECOND_COUNTER_MASK != 0)
            {
                return false;
            } else if core::unlikely(loaded & Self::SECOND_COUNTER_MASK == Self::SECOND_COUNTER_MASK) {
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
            if loaded & Self::LOCK_MASK != Self::LOCK_UNLOCKED {
                if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_BUSY {
                    loaded = self.state.load(Ordering::Relaxed);
                    hint::spin_loop();
                } else {
                    atomic::fence(Ordering::Acquire);
                    match self
                        .state
                        .compare_exchange_weak(loaded, Self::QUEUE_BUSY | (loaded & Self::LOCK_MASK), Ordering::Acquire, Ordering::Relaxed)
                    {
                        Ok(_) => {
                            self.wait(&mut loaded);
                            loaded = self.state.load(Ordering::Relaxed);
                        }
                        Err(current) => {
                            loaded = current;
                            hint::spin_loop();
                        }
                    }
                }
            } else {
                match self.state.compare_exchange_weak(
                    loaded,
                    (loaded & Self::QUEUE_STATE_MASK) | Self::LOCK_GLOBAL_WRITER,
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
            if loaded & Self::LOCK_MASK != Self::LOCK_UNLOCKED {
                return false;
            } else {
                match self.state.compare_exchange_weak(
                    loaded,
                    (loaded & Self::QUEUE_STATE_MASK) | Self::LOCK_GLOBAL_WRITER,
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
        while let Err(current) =
            self.state
                .compare_exchange_weak(loaded, Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK), Ordering::Release, Ordering::Relaxed)
        {
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
        while let Err(current) =
            self.state
                .compare_exchange_weak(loaded, Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK), Ordering::Release, Ordering::Relaxed)
        {
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
        while let Err(current) =
            self.state
                .compare_exchange_weak(loaded, Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK), Ordering::Release, Ordering::Relaxed)
        {
            loaded = current;
            hint::spin_loop();
        }
    }

    pub(crate) unsafe fn drop_global_writer_unchecked(&self) {
        let mut loaded = self.state.load(Ordering::Relaxed);
        loop {
            loaded = if loaded & Self::QUEUE_STATE_MASK == Self::QUEUE_AVAILABLE {
                if let Err(current) = self
                    .state
                    .compare_exchange_weak(loaded, Self::QUEUE_BUSY | Self::LOCK_UNLOCKED, Ordering::Acquire, Ordering::Relaxed)
                {
                    current
                } else {
                    break;
                }
            } else {
                self.state.load(Ordering::Relaxed)
            };
            hint::spin_loop();
        }

        // SAFETY: `state` provides synchronization - no other thread
        //         can access the queue at this point.
        unsafe { (*self.queue.get()).wake_all() };
        while let Err(current) =
            self.state
                .compare_exchange_weak(loaded, Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK), Ordering::Release, Ordering::Relaxed)
        {
            loaded = current;
            hint::spin_loop();
        }
    }

    #[cfg(feature = "downgrade")]
    pub(crate) unsafe fn downgrade_writer_unchecked(&self) {
        let mut loaded = self.state.load(Ordering::Relaxed);
        loop {
            if core::unlikely(loaded & Self::FIRST_COUNTER_MASK == Self::FIRST_COUNTER_MASK) {
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
        while let Err(current) =
            self.state
                .compare_exchange_weak(loaded, Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK), Ordering::Release, Ordering::Relaxed)
        {
            loaded = current;
            hint::spin_loop();
        }
    }

    #[cfg(feature = "downgrade")]
    pub(crate) unsafe fn downgrade_global_writer_unchecked(&self) {
        let mut loaded = self.state.load(Ordering::Relaxed);
        while let Err(current) = self
            .state
            .compare_exchange_weak(loaded, Self::QUEUE_BUSY | Self::SECOND_COUNTER_ONE, Ordering::Acquire, Ordering::Relaxed)
        {
            loaded = current;
            hint::spin_loop();
        }

        // SAFETY: `state` provides synchronization - no other thread
        //         can access the queue at this point.
        unsafe { (*self.queue.get()).wake_all() };

        while let Err(current) =
            self.state
                .compare_exchange_weak(loaded, Self::QUEUE_AVAILABLE | (loaded & Self::LOCK_MASK), Ordering::Release, Ordering::Relaxed)
        {
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
        ReadersAndGlobalReaders { readers: NonZeroU16, global_readers: NonZeroU16 },
        ReadersAndWriters { readers: NonZeroU16, writers: NonZeroU16 },
    }

    impl InnerRwLock {
        pub(crate) fn state(&self) -> LockState {
            let loaded = self.state.load(Ordering::Relaxed);
            let first_counter = NonZeroU16::new(((loaded & Self::FIRST_COUNTER_MASK) >> Self::FIRST_COUNTER_MASK.trailing_zeros()) as _);
            let second_counter = NonZeroU16::new(((loaded & Self::SECOND_COUNTER_MASK) >> Self::SECOND_COUNTER_MASK.trailing_zeros()) as _);
            match (loaded & Self::LOCK_STATE_MASK == Self::LOCK_MUTABLE, first_counter, second_counter) {
                (false, None, None) => LockState::Empty,
                (false, Some(readers), None) => LockState::Readers(readers),
                (false, None, Some(global_readers)) => LockState::GlobalReaders(global_readers),
                (true, None, Some(writers)) => LockState::Writers(writers),
                (true, None, None) => LockState::GlobalWriter,
                (false, Some(readers), Some(global_readers)) => LockState::ReadersAndGlobalReaders { readers, global_readers },
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
            assert_matches!(lock.state(), LockState::ReadersAndWriters { readers: ONE, writers: ONE });
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
            assert_matches!(lock.state(), LockState::ReadersAndWriters { readers: ONE, writers: ONE });

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
                    assert_matches!(lock.state(), LockState::ReadersAndWriters { readers: ONE, writers: ONE });

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
                    assert_matches!(lock.state(), LockState::ReadersAndWriters { readers: ONE, writers: ONE });

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

    mod benches {
        use super::super::InnerRwLock;
        use std::{
            mem::{self, MaybeUninit},
            sync::{
                Barrier,
                atomic::{AtomicU128, Ordering},
            },
            thread,
            time::Instant,
        };

        #[derive(Clone, Copy, Default)]
        struct TimeTable<T> {
            read: T,
            read_all: T,
            write: T,
            write_all: T,
        }

        #[derive(Clone, Copy, Default)]
        struct Statistic<T> {
            mean: T,
            std: T,
        }

        fn bench_template<const NTRIALS: usize, const NTHREADS: usize, FWorkers, FMain>(workers: FWorkers, main: FMain) -> TimeTable<Statistic<f64>>
        where
            FWorkers: Fn(&InnerRwLock, &Barrier, &Barrier, &AtomicU128, &Instant, &mut TimeTable<u128>, bool) + Sync,
            FMain: Fn(&InnerRwLock, &Barrier, &AtomicU128, &Instant),
        {
            let lock = InnerRwLock::new();
            let barrier_all = Barrier::new(NTHREADS + 1);
            let barrier_workers = Barrier::new(NTHREADS);
            let instant = AtomicU128::new(0);
            let instant_start = Instant::now();

            let mut times = Box::<[[TimeTable<u128>; NTRIALS]]>::new_uninit_slice(NTHREADS);
            for thread_trials in times.iter_mut() {
                let thread_trials = unsafe { mem::transmute::<_, &mut [MaybeUninit<TimeTable<u128>>; NTRIALS]>(thread_trials) };
                thread_trials.fill(MaybeUninit::new(TimeTable::default()));
            }
            let mut times = unsafe { times.assume_init() };

            thread::scope(|s| {
                for (i, trial_times) in times.iter_mut().enumerate() {
                    let lock = &lock;
                    let barrier_all = &barrier_all;
                    let barrier_workers = &barrier_workers;
                    let instant = &instant;
                    let instant_start = &instant_start;
                    let workers = &workers;
                    s.spawn(move || {
                        for trial_time_table in trial_times.iter_mut() {
                            workers(lock, barrier_all, barrier_workers, instant, instant_start, trial_time_table, i == 0)
                        }
                    });
                }

                for _ in 0..NTRIALS {
                    main(&lock, &barrier_all, &instant, &instant_start);
                }
            });

            macro_rules! square {
                ($n:expr) => {{ $n * $n }};
            }

            let mut stats = TimeTable::<Statistic<f64>>::default();
            for thread_trials in times.iter() {
                for trial in thread_trials {
                    stats.read.mean += trial.read as f64;
                    stats.read.std += square!(trial.read) as f64;
                    stats.read_all.mean += trial.read_all as f64;
                    stats.read_all.std += square!(trial.read_all) as f64;
                    stats.write.mean += trial.write as f64;
                    stats.write.std += square!(trial.write) as f64;
                    stats.write_all.mean += trial.write_all as f64;
                    stats.write_all.std += square!(trial.write_all) as f64;
                }
            }
            let total_runs = const { NTHREADS * NTRIALS } as f64;
            stats.read.mean /= total_runs;
            stats.read.std = ((stats.read.std / total_runs - square!(stats.read.mean)) / total_runs).sqrt();
            stats.read_all.mean /= total_runs;
            stats.read_all.std = ((stats.read_all.std / total_runs - square!(stats.read_all.mean)) / total_runs).sqrt();
            stats.write.mean /= total_runs;
            stats.write.std = ((stats.write.std / total_runs - square!(stats.write.mean)) / total_runs).sqrt();
            stats.write_all.mean /= NTRIALS as f64;
            stats.write_all.std = ((stats.write_all.std / (NTRIALS as f64) - square!(stats.write_all.mean)) / (NTRIALS as f64)).sqrt();
            stats
        }

        #[test]
        fn all() {
            const NTRIALS: usize = 2_000_000;
            const NTHREADS: usize = 8;

            let read = bench_template::<NTRIALS, NTHREADS, _, _>(
                |lock, barrier_all, barrier_workers, instant, instant_start, time_table, is_leading| {
                    // ...0
                    barrier_all.wait();
                    // 1
                    let before = Instant::now();
                    lock.read();
                    time_table.read = Instant::now().duration_since(before).as_nanos();
                    barrier_workers.wait();
                    // 2
                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    barrier_workers.wait();
                    // 3
                    let before = Instant::now();
                    lock.read_all();
                    time_table.read_all = Instant::now().duration_since(before).as_nanos();
                    barrier_workers.wait();
                    // 4
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    barrier_workers.wait();
                    // 5
                    let before = Instant::now();
                    lock.write();
                    time_table.write = Instant::now().duration_since(before).as_nanos();
                    barrier_workers.wait();
                    // 6
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    barrier_all.wait();
                    // 7
                    if is_leading {
                        lock.write_all();
                        time_table.write_all = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                        unsafe {
                            lock.drop_global_writer_unchecked();
                        }
                    }
                    barrier_all.wait();
                },
                |lock, barrier_all, instant, instant_start| {
                    // 0
                    lock.read();
                    barrier_all.wait();
                    // ...1-6
                    barrier_all.wait();
                    // 7
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    barrier_all.wait();
                },
            );
            let read_all = bench_template::<NTRIALS, NTHREADS, _, _>(
                |lock, barrier_all, barrier_workers, instant, instant_start, time_table, is_leading| {
                    // ...0
                    barrier_all.wait();
                    // 1
                    let before = Instant::now();
                    lock.read();
                    time_table.read = Instant::now().duration_since(before).as_nanos();
                    barrier_workers.wait();
                    // 2
                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    barrier_workers.wait();
                    // 3
                    let before = Instant::now();
                    lock.read_all();
                    time_table.read_all = Instant::now().duration_since(before).as_nanos();
                    barrier_workers.wait();
                    // 4
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    barrier_all.wait();
                    // 5
                    lock.write();
                    time_table.write = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                    barrier_workers.wait();
                    // 6
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    barrier_all.wait();
                    // ...7
                    barrier_all.wait();
                    // 8
                    if is_leading {
                        lock.write_all();
                        time_table.write_all = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                        unsafe {
                            lock.drop_global_writer_unchecked();
                        }
                    }
                    barrier_all.wait();
                },
                |lock, barrier_all, instant, instant_start| {
                    // 0
                    lock.read_all();
                    barrier_all.wait();
                    // ...1-4
                    barrier_all.wait();
                    // 5-6
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    barrier_all.wait();
                    // 7
                    lock.read_all();
                    barrier_all.wait();
                    // 8
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    barrier_all.wait();
                },
            );
            let write = bench_template::<NTRIALS, NTHREADS, _, _>(
                |lock, barrier_all, barrier_workers, instant, instant_start, time_table, is_leading| {
                    // ...0
                    barrier_all.wait();
                    // 1
                    let before = Instant::now();
                    lock.read();
                    time_table.read = before.elapsed().as_nanos();
                    barrier_workers.wait();
                    // 2
                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    barrier_all.wait();
                    // 3
                    lock.read_all();
                    time_table.read_all = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                    barrier_workers.wait();
                    // 4
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    barrier_all.wait();
                    // ...5
                    barrier_all.wait();
                    // 6
                    let before = Instant::now();
                    lock.write();
                    time_table.write = before.elapsed().as_nanos();
                    barrier_workers.wait();
                    // 7
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    barrier_all.wait();
                    // 8
                    if is_leading {
                        lock.write_all();
                        time_table.write_all = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                        unsafe {
                            lock.drop_global_writer_unchecked();
                        }
                    }
                    barrier_all.wait();
                },
                |lock, barrier_all, instant, instant_start| {
                    // 0
                    lock.write();
                    barrier_all.wait();
                    // ...1-2
                    barrier_all.wait();
                    // 3-4
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    barrier_all.wait();
                    // 5
                    lock.write();
                    barrier_all.wait();
                    // ...6-7
                    barrier_all.wait();
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    barrier_all.wait();
                },
            );
            let write_all = bench_template::<NTRIALS, NTHREADS, _, _>(
                |lock, barrier_all, barrier_workers, instant, instant_start, time_table, is_leading| {
                    // ...0
                    barrier_all.wait();
                    // 1
                    lock.read();
                    time_table.read = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                    barrier_workers.wait();
                    // 2
                    unsafe {
                        lock.drop_reader_unchecked();
                    }
                    barrier_all.wait();
                    // ...3
                    barrier_all.wait();
                    // 4
                    lock.read_all();
                    time_table.read_all = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                    barrier_workers.wait();
                    // 5
                    unsafe {
                        lock.drop_global_reader_unchecked();
                    }
                    barrier_all.wait();
                    // ...6
                    barrier_all.wait();
                    // 7
                    lock.write();
                    time_table.write = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                    barrier_workers.wait();
                    // 8
                    unsafe {
                        lock.drop_writer_unchecked();
                    }
                    barrier_all.wait();
                    // ...9
                    barrier_all.wait();
                    if is_leading {
                        lock.write_all();
                        time_table.write_all = instant_start.elapsed().as_nanos() - instant.load(Ordering::Relaxed);
                        unsafe {
                            lock.drop_global_writer_unchecked();
                        }
                    }
                    barrier_all.wait();
                },
                |lock, barrier_all, instant, instant_start| {
                    // 0
                    lock.write_all();
                    barrier_all.wait();
                    // 1-2
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_global_writer_unchecked();
                    }
                    barrier_all.wait();
                    // 3
                    lock.write_all();
                    barrier_all.wait();
                    // 4-5
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_global_writer_unchecked();
                    }
                    barrier_all.wait();
                    // 6
                    lock.write_all();
                    barrier_all.wait();
                    // 7-8
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_global_writer_unchecked();
                    }
                    barrier_all.wait();
                    // 9
                    lock.write_all();
                    barrier_all.wait();
                    instant.store(instant_start.elapsed().as_nanos(), Ordering::Relaxed);
                    unsafe {
                        lock.drop_global_writer_unchecked();
                    }
                    barrier_all.wait();
                },
            );
            println!(
                "{:^21}|{:^21}|{:^21}|{:^21}|{:^21}\n\
                 ---------------------|---------------------|---------------------|---------------------|---------------------\n\
                 {:^21}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}\n\
                 {:^21}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}\n\
                 {:^21}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}\n\
                 {:^21}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}|{:>9.1} ± {:<9.1}\n\
                ",
                "create\\drop",
                "read",
                "read_all",
                "write",
                "write_all",
                "read",
                read.read.mean,
                read.read.std,
                read.read_all.mean,
                read.read_all.std,
                read.write.mean,
                read.write.std,
                read.write_all.mean,
                read.write_all.std,
                "read_all",
                read_all.read.mean,
                read_all.read.std,
                read_all.read_all.mean,
                read_all.read_all.std,
                read_all.write.mean,
                read_all.write.std,
                read_all.write_all.mean,
                read_all.write_all.std,
                "write",
                write.read.mean,
                write.read.std,
                write.read_all.mean,
                write.read_all.std,
                write.write.mean,
                write.write.std,
                write.write_all.mean,
                write.write_all.std,
                "write_all",
                write_all.read.mean,
                write_all.read.std,
                write_all.read_all.mean,
                write_all.read_all.std,
                write_all.write.mean,
                write_all.write.std,
                write_all.write_all.mean,
                write_all.write_all.std,
            )
        }
    }
}
