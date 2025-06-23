#![allow(dead_code)]
pub mod slice_rw_lock {
    pub mod inner {
        use std::{
            hint,
            num::NonZero,
            process,
            sync::{Condvar, Mutex},
        };

        #[cfg(target_pointer_width = "32")]
        #[allow(non_camel_case_types)]
        type counter = u8;
        #[cfg(target_pointer_width = "64")]
        #[allow(non_camel_case_types)]
        type counter = u16;

        #[derive(Clone, Copy)]
        enum CompetingAccess {
            SliceReaders(NonZero<counter>),
            Writers(NonZero<counter>),
            None,
        }

        #[repr(u8)]
        #[derive(Clone, Copy)]
        enum State {
            Open,
            SliceWriter,
            Other {
                readers: counter,
                slice_readers_or_writers: CompetingAccess,
            },
        }

        pub(super) struct InnerSliceRwLock {
            state: Mutex<State>,
            readers_waker: Condvar,
            slice_readers_waker: Condvar,
            writers_waker: Condvar,
            slice_writers_waker: Condvar,
        }

        impl InnerSliceRwLock {
            pub(super) fn read(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe {
                    self.readers_waker
                        .wait_while(self.state.lock().unwrap_unchecked(), |&mut state| {
                            matches!(state, State::SliceWriter)
                        })
                        .unwrap_unchecked()
                };
                match &mut *guard {
                    State::Open => {
                        *guard = State::Other {
                            readers: 1,
                            slice_readers_or_writers: CompetingAccess::None,
                        }
                    }
                    State::Other {
                        readers: counter::MAX, ..
                    } => process::abort(),
                    State::Other { readers, .. } => *readers = unsafe { readers.unchecked_add(1) }, // SAFETY: Checked that overflow cannot occur in the case above
                    State::SliceWriter =>
                    // SAFETY: The `Condvar` is guaranteed to return a guard when the state is not `State::SliceWriter`
                    unsafe { hint::unreachable_unchecked() },
                }
            }

            pub(super) fn read_slice(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe {
                    self.slice_readers_waker
                        .wait_while(self.state.lock().unwrap_unchecked(), |&mut state| {
                            matches!(
                                state,
                                State::SliceWriter
                                    | State::Other {
                                        slice_readers_or_writers: CompetingAccess::Writers(_),
                                        ..
                                    }
                            )
                        })
                        .unwrap_unchecked()
                };
                match &mut *guard {
                    State::Open => {
                        *guard = State::Other {
                            readers: 0,
                            // SAFETY: `1` is clearly within the allowed range of `NonZero<counter>`
                            slice_readers_or_writers: CompetingAccess::SliceReaders(unsafe {
                                NonZero::<_>::new_unchecked(1)
                            }),
                        }
                    }
                    State::Other {
                        slice_readers_or_writers: slice_readers @ CompetingAccess::None,
                        ..
                    } => *slice_readers = CompetingAccess::SliceReaders(unsafe { NonZero::<_>::new_unchecked(1) }), // SAFETY: See comment above
                    State::Other {
                        slice_readers_or_writers: CompetingAccess::SliceReaders(NonZero::<counter>::MAX),
                        ..
                    } => process::abort(),
                    State::Other {
                        slice_readers_or_writers: CompetingAccess::SliceReaders(slice_readers),
                        ..
                    } => *slice_readers = unsafe { NonZero::<_>::new_unchecked(slice_readers.get().unchecked_add(1)) }, // SAFETY: Checked that overflow cannot occur in the case above
                    _ =>
                    // SAFETY: The `Condvar` is guaranteed to return a guard when the state
                    // is neither `State::SliceWriter` nor `State::Other {slice_readers_or_writers: CompetingAccess::Writers(_), ..}`
                    unsafe { hint::unreachable_unchecked() },
                }
            }

            pub(super) fn write(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe {
                    self.writers_waker
                        .wait_while(self.state.lock().unwrap_unchecked(), |&mut state| {
                            matches!(
                                state,
                                State::SliceWriter
                                    | State::Other {
                                        slice_readers_or_writers: CompetingAccess::SliceReaders(_),
                                        ..
                                    }
                            )
                        })
                        .unwrap_unchecked()
                };
                match &mut *guard {
                    State::Open => {
                        *guard = State::Other {
                            readers: 0,
                            // SAFETY: `1` is clearly within the allowed range of `NonZero<counter>`
                            slice_readers_or_writers: CompetingAccess::Writers(unsafe {
                                NonZero::<_>::new_unchecked(1)
                            }),
                        }
                    }
                    State::Other {
                        slice_readers_or_writers: writers @ CompetingAccess::None,
                        ..
                    } => *writers = CompetingAccess::Writers(unsafe { NonZero::<_>::new_unchecked(1) }), // SAFETY: See comment above
                    State::Other {
                        slice_readers_or_writers: CompetingAccess::Writers(NonZero::<counter>::MAX),
                        ..
                    } => process::abort(),
                    State::Other {
                        slice_readers_or_writers: CompetingAccess::Writers(writers),
                        ..
                    } => *writers = unsafe { NonZero::<_>::new_unchecked(writers.get().unchecked_add(1)) }, // SAFETY: Checked that overflow cannot occur in the case above
                    _ =>
                    // SAFETY: The `Condvar` is guaranteed to return a guard when the state
                    // is neither `State::SliceWriter` nor `State::Other {slice_readers_or_writers: CompetingAccess::SliceReaders(_), ..}`
                    unsafe { hint::unreachable_unchecked() },
                }
            }

            pub(super) fn write_slice(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe {
                    self.slice_writers_waker
                        .wait_while(self.state.lock().unwrap_unchecked(), |&mut state| {
                            !matches!(state, State::Open)
                        })
                        .unwrap_unchecked()
                };
                *guard = State::SliceWriter;
            }

            // Calling this function when there are no readers is undefined behaviour
            pub(super) unsafe fn drop_reader(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe { self.state.lock().unwrap_unchecked() };
                match &mut *guard {
                    State::Other {
                        readers: 1,
                        slice_readers_or_writers: CompetingAccess::None,
                    } => {
                        *guard = State::Open;
                        self.slice_writers_waker.notify_one();
                    },
                    // SAFETY: Assuming the number of readers is greater than zero, decrementing the counter will not result in an overflow
                    State::Other { readers: readers @ 1.., .. } => *readers = unsafe { readers.unchecked_sub(1) },
                    _ => unsafe { hint::unreachable_unchecked() },
                }
            }

            // CAlling this function when there are no slice readers is undefined behaviour
            pub(super) unsafe fn drop_slice_reader(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe { self.state.lock().unwrap_unchecked() };
                match &mut *guard {
                    State::Other {
                        readers: 0,
                        slice_readers_or_writers: CompetingAccess::SliceReaders(NonZero::<counter>::MIN),
                    } => {
                        *guard = State::Open;
                        self.slice_writers_waker.notify_one();
                        self.writers_waker.notify_all();
                    },
                    State::Other {
                        slice_readers_or_writers: slice_readers @ CompetingAccess::SliceReaders(NonZero::<counter>::MIN),
                        ..
                    } => {
                        *slice_readers = CompetingAccess::None;
                        self.writers_waker.notify_all();
                    },
                    State::Other {
                        slice_readers_or_writers: CompetingAccess::SliceReaders(slice_readers),
                        ..
                    } => 
                    // SAFETY: Assuming there are slice readers, we checked above that there are more than one
                    *slice_readers = unsafe { NonZero::<_>::new_unchecked(slice_readers.get().unchecked_sub(1)) },
                    _ => unsafe { hint::unreachable_unchecked() },
                }
            }

            // Calling this function when there are no writers is undefined behaciour
            pub(super) unsafe fn drop_writer(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe { self.state.lock().unwrap_unchecked() };
                match &mut *guard {
                    State::Other {
                        readers: 0, 
                        slice_readers_or_writers: CompetingAccess::Writers(NonZero::<counter>::MIN)
                    } => {
                        *guard = State::Open; 
                        self.slice_writers_waker.notify_one();
                        self.slice_readers_waker.notify_all();
                    },
                    State::Other {
                        slice_readers_or_writers: writers @ CompetingAccess::Writers(NonZero::<counter>::MIN),
                        ..
                    } => {
                        *writers = CompetingAccess::None;
                        self.slice_readers_waker.notify_all();
                    },
                    State::Other {
                        slice_readers_or_writers: CompetingAccess::Writers(writers),
                        ..
                    } =>
                    // SAFETY: Assuming there are writers, we checked above that there are more than one
                    *writers = unsafe { NonZero::<_>::new_unchecked(writers.get().unchecked_sub(1)) },
                    _ => unsafe { hint::unreachable_unchecked() }
                }
            }

            // Calling this function when there is no slice writer is undefined behaviour
            pub(super) unsafe fn drop_slice_writer(&self) {
                // SAFETY: Cannot panic while holding a guard to `self.state`
                let mut guard = unsafe { self.state.lock().unwrap_unchecked() };
                *guard = State::Open;
                self.readers_waker.notify_all();
                self.slice_readers_waker.notify_all();
                self.slice_writers_waker.notify_all();
            }
        }
    }
}

#[cfg(test)]
mod tests {
}
