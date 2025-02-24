#![allow(dead_code)]
pub mod slice_rw_lock {
    mod elem {
        use std::{
            marker::PhantomData,
            ptr::NonNull,
            sync::{
                atomic::{fence, AtomicBool, AtomicUsize, Ordering}, Condvar, LockResult, Mutex, PoisonError
            }, thread::panicking,
        };

        struct Metadata {
            counter: AtomicUsize,
            poisoned: AtomicBool,
            guard: (Mutex<RwVariants<usize>>, RwVariants<Condvar>),
        }

        struct Data<T> {
            metadata: Metadata,
            data: [T],
        }

        struct RwVariants<T> {
            readers: T,
            slice_readers: T,
            writers: T,
            slice_writers: T,
        }

        pub struct ElemRwLock<T> {
            idx: usize,
            data_ptr: NonNull<Data<T>>,
        }

        impl<T> ElemRwLock<T> {
            pub fn read(&self) -> LockResult<ElemRwLockReadGuard<'_, T>> {
                let Data {
                    metadata:
                        Metadata {
                            poisoned,
                            guard: (lock, RwVariants { readers, .. }),
                            ..
                        },
                    ..
                } = unsafe { &self.data_ptr.as_ref() };
                let mut guard = unsafe {
                    readers
                        .wait(lock.lock().unwrap_unchecked())
                        .unwrap_unchecked()
                };
                guard.readers += 1;
                drop(guard);

                let ret = ElemRwLockReadGuard {
                    data_ptr: self.data_ptr,
                    phantom: PhantomData,
                };
                if poisoned.load(Ordering::Relaxed) {
                    Err(PoisonError::new(ret))
                } else {
                    Ok(ret)
                }
            }

            pub fn read_slice(&self) -> LockResult<ElemRwLockReadSliceGuard<'_, T>> {
                let Data {
                    metadata:
                        Metadata {
                            poisoned,
                            guard: (lock, RwVariants { slice_readers, .. }),
                            ..
                        },
                    ..
                } = unsafe { &self.data_ptr.as_ref() };
                let mut guard = unsafe {
                    slice_readers
                        .wait_while(
                            lock.lock().unwrap_unchecked(),
                            |&mut RwVariants {
                                 slice_writers,
                                 writers,
                                 ..
                             }| slice_writers > 0 && writers > 0,
                        )
                        .unwrap_unchecked()
                };
                guard.slice_readers += 1;
                drop(guard);

                let ret = ElemRwLockReadSliceGuard {
                    data_ptr: self.data_ptr,
                    phantom: PhantomData,
                };
                if poisoned.load(Ordering::Relaxed) {
                    Err(PoisonError::new(ret))
                } else {
                    Ok(ret)
                }
            }

            pub fn write(&mut self) -> LockResult<ElemRwLockWriteGuard<'_, T>> {
                let Data {
                    metadata:
                        Metadata {
                            poisoned,
                            guard: (lock, RwVariants { writers, .. }),
                            ..
                        },
                    ..
                } = unsafe { &self.data_ptr.as_ref() };
                let mut guard = unsafe {
                    writers
                        .wait(lock.lock().unwrap_unchecked())
                        .unwrap_unchecked()
                };
                guard.writers += 1;
                drop(guard);

                let ret = ElemRwLockWriteGuard {
                    data_ptr: self.data_ptr,
                    phantom: PhantomData,
                };
                if poisoned.load(Ordering::Relaxed) {
                    Err(PoisonError::new(ret))
                } else {
                    Ok(ret)
                }
            }

            pub fn write_slice(&mut self) -> LockResult<ElemRwLockWriteSliceGuard<'_, T>> {
                let Data {
                    metadata:
                        Metadata {
                            poisoned,
                            guard: (lock, RwVariants { slice_writers, .. }),
                            ..
                        },
                    ..
                } = unsafe { &self.data_ptr.as_ref() };
                let mut guard = unsafe {
                    slice_writers
                        .wait_while(
                            lock.lock().unwrap_unchecked(),
                            |&mut RwVariants {
                                 readers,
                                 slice_readers,
                                 ..
                             }| readers > 0 && slice_readers > 0,
                        )
                        .unwrap_unchecked()
                };
                guard.slice_writers += 1;
                drop(guard);

                let ret = ElemRwLockWriteSliceGuard {
                    data_ptr: self.data_ptr,
                    phantom: PhantomData,
                };
                if poisoned.load(Ordering::Relaxed) {
                    Err(PoisonError::new(ret))
                } else {
                    Ok(ret)
                }
            }
        }

        impl<T> Drop for ElemRwLock<T> {
            fn drop(&mut self) {
                let Data {
                    metadata: Metadata { counter, .. },
                    ..
                } = unsafe { &self.data_ptr.as_ref() };
                if counter.fetch_sub(1, Ordering::Release) != 1 {
                    return;
                }

                fence(Ordering::Acquire);
                let _ = unsafe { Box::from_raw(self.data_ptr.as_ptr()) };
            }
        }

        pub struct ElemRwLockReadGuard<'a, T> {
            data_ptr: NonNull<Data<T>>,
            phantom: PhantomData<&'a T>,
        }

        impl<'a, T> Drop for ElemRwLockReadGuard<'a, T> {
            fn drop(&mut self) {
                let Data {
                    metadata:
                        Metadata {
                            guard: (lock, RwVariants { slice_writers, .. }),
                            ..
                        },
                    ..
                } = unsafe { &self.data_ptr.as_ref() };
                let mut guard = unsafe { lock.lock().unwrap_unchecked() };
                guard.readers = unsafe { guard.readers.unchecked_sub(1) };
                if guard.readers == 0 {
                    slice_writers.notify_all();
                }
            }
        }

        pub struct ElemRwLockReadSliceGuard<'a, T> {
            data_ptr: NonNull<Data<T>>,
            phantom: PhantomData<&'a [T]>,
        }

        impl<'a, T> Drop for ElemRwLockReadSliceGuard<'a, T> {
            fn drop(&mut self) {
                let Data {
                    metadata:
                        Metadata {
                            guard:
                                (
                                    lock,
                                    RwVariants {
                                        writers,
                                        slice_writers,
                                        ..
                                    },
                                ),
                            ..
                        },
                    ..
                } = unsafe { &self.data_ptr.as_ref() };
                let mut guard = unsafe { lock.lock().unwrap_unchecked() };
                guard.slice_readers = unsafe { guard.slice_readers.unchecked_sub(1) };
                if guard.slice_readers == 0 {
                    writers.notify_all();
                    slice_writers.notify_all();
                }
            }
        }

        pub struct ElemRwLockWriteGuard<'a, T> {
            data_ptr: NonNull<Data<T>>,
            phantom: PhantomData<&'a mut T>,
        }

        impl<'a, T> Drop for ElemRwLockWriteGuard<'a, T> {
            fn drop(&mut self) {
                let Data {metadata: Metadata{poisoned, guard: (lock, RwVariants{slice_readers, ..}), ..}, ..} = unsafe { self.data_ptr.as_ref() };
                if panicking() {
                    poisoned.store(true, Ordering::Release);
                }
                let mut guard = unsafe { lock.lock().unwrap_unchecked() };
                guard.writers = unsafe { guard.writers.unchecked_sub(1) };
                if guard.writers == 0 {
                    slice_readers.notify_all();
                }
            }
        }

        pub struct ElemRwLockWriteSliceGuard<'a, T> {
            data_ptr: NonNull<Data<T>>,
            phantom: PhantomData<&'a mut [T]>,
        }
        
        impl<'a, T> Drop for ElemRwLockWriteSliceGuard<'a, T> {
            fn drop(&mut self) {
                let Data {metadata: Metadata{poisoned, guard: (lock, RwVariants{readers, slice_readers, ..}), ..}, ..} = unsafe { &self.data_ptr.as_ref() };
                if panicking() {
                    poisoned.store(true, Ordering::Release);
                }
                let mut guard = unsafe { lock.lock().unwrap_unchecked() };
                guard.slice_writers = unsafe { guard.slice_writers.unchecked_sub(1) };
                if guard.slice_writers == 0 {
                    readers.notify_all();
                    slice_readers.notify_all();
                }
            }
        }
    
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
