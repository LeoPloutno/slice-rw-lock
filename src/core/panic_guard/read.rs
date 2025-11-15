use crate::core::InnerRwLock;

/// A struct that handles locking and unlocking a lock locked with shared subfield read access, despite panics.
#[repr(transparent)]
#[must_use]
#[clippy::has_significant_drop]
pub(crate) struct ReadPanicGuard<'a>(&'a InnerRwLock);

impl<'a> ReadPanicGuard<'a> {
    /// Constructs a guard that will call [`drop_reader_unchecked`] for
    /// the provided lock upon destruction.
    ///
    /// # Safety
    /// The lock must be locked with `read` access when the returned
    /// guard is destroyed.
    ///
    /// [`drop_reader_unchecked`]: crate::core::rw_lock::InnerRwLock::drop_reader_unchecked
    #[inline]
    pub(crate) const unsafe fn new(lock: &'a InnerRwLock) -> Self {
        Self(lock)
    }
}

impl<'a> Drop for ReadPanicGuard<'a> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: User-upheld invariant.
        unsafe {
            self.0.drop_reader_unchecked();
        }
    }
}
