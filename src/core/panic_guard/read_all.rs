use crate::core::InnerRwLock;

/// A struct that handles locking and unlocking a lock locked with shared global read access, despite panics.
#[repr(transparent)]
#[must_use]
#[clippy::has_significant_drop]
pub(crate) struct ReadAllPanicGuard<'a>(&'a InnerRwLock);

impl<'a> ReadAllPanicGuard<'a> {
    /// Constructs a guard that will call [`drop_global_reader_unchecked`] for
    /// the provided lock upon destruction.
    ///
    /// # Safety
    /// The lock must be locked with `read_all` access when the returned
    /// guard is destroyed.
    ///
    /// [`drop_global_reader_unchecked`]: crate::core::rw_lock::InnerRwLock::drop_global_reader_unchecked
    #[inline]
    pub(crate) const unsafe fn new(lock: &'a InnerRwLock) -> Self {
        Self(lock)
    }
}

impl<'a> Drop for ReadAllPanicGuard<'a> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: User-upheld invariant.
        unsafe {
            self.0.drop_global_reader_unchecked();
        }
    }
}
