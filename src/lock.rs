use std::sync::atomic::{AtomicIsize, Ordering};

/// A simplified RwLock implementation which only supports voluntary locking.
pub struct RwLock {
    state: AtomicIsize,
}

impl RwLock {
    /// Construct a new lock that's in an unlocked state.
    pub const fn new() -> Self {
        Self {
            state: AtomicIsize::new(0),
        }
    }

    /// Construct a new lock that is already locked.
    pub const fn locked() -> Self {
        Self {
            state: AtomicIsize::new(-std::isize::MAX),
        }
    }

    /// Try to lock exclusively.
    pub fn try_lock_exclusive(&self) -> bool {
        let last = self.state.fetch_sub(std::isize::MAX, Ordering::AcqRel);

        if last != 0 {
            // try again later
            self.state.fetch_add(std::isize::MAX, Ordering::AcqRel);
            return false;
        }

        if last == std::isize::MIN {
            // Sentinel value in case we observe a value that has wrapped
            // around. This is such a abnormal state that there's not much
            // we _can_ do. Abort the process.
            std::process::abort();
        }

        true
    }

    pub fn try_lock_exclusive_guard(&self) -> Option<LockExclusiveGuard<'_>> {
        if self.try_lock_exclusive() {
            Some(LockExclusiveGuard { lock: self })
        } else {
            None
        }
    }

    /// Unlock shared access.
    pub fn unlock_exclusive(&self) {
        let old = self.state.fetch_add(std::isize::MAX, Ordering::AcqRel);
        debug_assert!(old >= -std::isize::MAX && old < 0);
    }

    /// Try to lock shared.
    pub fn try_lock_shared(&self) -> bool {
        let existing = self.state.fetch_add(1, Ordering::AcqRel);

        if existing < 0 {
            self.state.fetch_sub(1, Ordering::AcqRel);
            return false;
        }

        if existing == std::isize::MAX {
            // Sentinel value in case we observe a value that has wrapped
            // around. This is such a abnormal state that there's not much
            // we _can_ do. Abort the process.
            std::process::abort();
        }

        true
    }

    /// Try to acquire a shared lock with a guard.
    pub fn try_lock_shared_guard(&self) -> Option<LockSharedGuard<'_>> {
        if self.try_lock_shared() {
            Some(LockSharedGuard { lock: self })
        } else {
            None
        }
    }

    /// Unlock shared access.
    pub fn unlock_shared(&self) {
        self.state.fetch_sub(1, Ordering::AcqRel);
    }
}

/// A lock guard for an exclusive lock.
pub struct LockExclusiveGuard<'a> {
    lock: &'a RwLock,
}

impl Drop for LockExclusiveGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_exclusive()
    }
}

/// A lock guard for a shared lock.
pub struct LockSharedGuard<'a> {
    lock: &'a RwLock,
}

impl Drop for LockSharedGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_shared()
    }
}
