pub(crate) use {
    alloc::Allocation,
    inner_rw_lock::InnerRwLock,
    panic_guard::{read::ReadPanicGuard, read_all::ReadAllPanicGuard, write::WritePanicGuard, write_all::WriteAllPanicGuard},
    state::State,
};

#[cold]
#[inline(always)]
pub(crate) fn unlikely(val: bool) -> bool {
    val
}

#[cold]
#[inline(always)]
pub(crate) fn cold_path() {}

mod alloc;

#[cfg_attr(feature = "atomic_wait", path = "core/atomic_wait.rs")]
#[cfg_attr(not(feature = "atomic_wait"), path = "core/std.rs")]
mod inner_rw_lock;

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

mod panic_guard {
    pub(super) mod read;
    pub(super) mod read_all;
    pub(super) mod write;
    pub(super) mod write_all;
}
