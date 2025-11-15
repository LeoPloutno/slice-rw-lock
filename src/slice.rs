pub(crate) mod array_chunks;
pub(crate) mod chunk_by;
pub(crate) mod chunks;
pub(crate) mod chunks_exact;
pub(crate) mod iter;
pub(crate) mod lock;
pub(crate) mod rarray_chunks;
pub(crate) mod rchunks;
pub(crate) mod rchunks_exact;
pub(crate) mod read_all;
pub(crate) mod rsplit;
pub(crate) mod rsplitn;
pub(crate) mod split;
pub(crate) mod split_inclusive;
pub(crate) mod splitn;
pub(crate) mod write;
pub(crate) mod write_all;
mod panic_guard {
    use crate::core::InnerRwLock;

    /// A struct that handles locking and unlocking a lock despite panics.
    #[repr(transparent)]
    #[must_use]
    #[clippy::has_significant_drop]
    pub(super) struct PanicWriteGuard<'a>(&'a InnerRwLock);

    impl<'a> PanicWriteGuard<'a> {
        /// Atomically locks `lock` with `write` access and constructs a guard that
        /// will be responsible for unlocking it when dropped.
        ///
        /// # Safety
        /// The guard returned by this function shall not be leaked in any way,
        /// otherwise undefined behaviour might occur.
        pub(super) unsafe fn new(lock: &'a InnerRwLock) -> Self {
            lock.write();
            Self(lock)
        }
    }

    impl<'a> Drop for PanicWriteGuard<'a> {
        fn drop(&mut self) {
            // SAFETY: Incremented the counter when created `self`.
            unsafe {
                self.0.drop_writer_unchecked();
            }
        }
    }
}
