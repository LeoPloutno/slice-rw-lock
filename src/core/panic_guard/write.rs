use crate::core::InnerRwLock;

/// A struct that handles locking and unlocking a lock locked with exclusive subfield write access, despite panics.
#[repr(transparent)]
#[must_use]
#[clippy::has_significant_drop]
pub(crate) struct WritePanicGuard<'a>(&'a InnerRwLock);

impl<'a> WritePanicGuard<'a> {
    /// Constructs a guard that will call [`drop_writer_unchecked`] for
    /// the provided lock upon destruction.
    ///
    /// # Safety
    /// The lock must be locked with `write` access when the returned
    /// guard is destroyed.
    ///
    /// [`drop_writer_unchecked`]: crate::core::rw_lock::InnerRwLock::drop_writer_unchecked
    #[inline]
    pub(crate) const unsafe fn new(lock: &'a InnerRwLock) -> Self {
        Self(lock)
    }
}

impl<'a> Drop for WritePanicGuard<'a> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: User-upheld invariant.
        unsafe {
            self.0.drop_writer_unchecked();
        }
    }
}
