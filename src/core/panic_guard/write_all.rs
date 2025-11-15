use crate::core::InnerRwLock;

/// A struct that handles locking and unlocking a lock locked with exclusive global write access, despite panics.
#[repr(transparent)]
#[must_use]
#[clippy::has_significant_drop]
pub(crate) struct WriteAllPanicGuard<'a>(&'a InnerRwLock);

impl<'a> WriteAllPanicGuard<'a> {
    /// Constructs a guard that will call [`drop_global_writer_unchecked`] for
    /// the provided lock upon destruction.
    ///
    /// # Safety
    /// The lock must be locked with `write_all` access when the returned
    /// guard is destroyed.
    ///
    /// [`drop_global_writer_unchecked`]: crate::core::rw_lock::InnerRwLock::drop_global_writer_unchecked
    #[inline]
    pub(crate) const unsafe fn new(lock: &'a InnerRwLock) -> Self {
        Self(lock)
    }
}

impl<'a> Drop for WriteAllPanicGuard<'a> {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: User-upheld invariant.
        unsafe {
            self.0.drop_global_writer_unchecked();
        }
    }
}
