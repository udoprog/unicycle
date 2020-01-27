#[cfg(not(feature = "parking-lot"))]
mod internals {
    //! Manual implementation using atomics.
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
        pub fn locked() -> Self {
            Self {
                state: AtomicIsize::new(-std::isize::MAX),
            }
        }

        /// Try to lock exclusively.
        pub fn try_lock_exclusive_immediate(&self) -> bool {
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

        /// Unlock shared access.
        pub fn unlock_exclusive_immediate(&self) {
            let old = self.state.fetch_add(std::isize::MAX, Ordering::AcqRel);
            debug_assert!(old >= -std::isize::MAX && old < 0);
        }

        /// Try to lock shared.
        pub fn try_lock_shared_immediate(&self) -> bool {
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

        /// Unlock shared access.
        pub fn unlock_shared_immediate(&self) {
            self.state.fetch_sub(1, Ordering::AcqRel);
        }
    }
}

#[cfg(feature = "parking-lot")]
mod internals {
    //! Implementation using raw locks from parking_lot.
    use lock_api::RawRwLock as _;

    /// A simplified RwLock implementation which only supports voluntary locking.
    pub struct RwLock {
        state: parking_lot::RawRwLock,
    }

    impl RwLock {
        /// Construct a new lock that's in an unlocked state.
        pub const fn new() -> Self {
            Self {
                state: parking_lot::RawRwLock::INIT,
            }
        }

        /// Construct a new lock that is already locked.
        pub fn locked() -> Self {
            let state = parking_lot::RawRwLock::INIT;
            state.lock_exclusive();

            Self { state }
        }

        /// Try to lock exclusively.
        pub fn try_lock_exclusive_immediate(&self) -> bool {
            self.state.try_lock_exclusive()
        }

        /// Unlock shared access.
        pub fn unlock_exclusive_immediate(&self) {
            self.state.unlock_exclusive()
        }

        /// Try to lock shared.
        pub fn try_lock_shared_immediate(&self) -> bool {
            self.state.try_lock_shared()
        }

        /// Unlock shared access.
        pub fn unlock_shared_immediate(&self) {
            self.state.unlock_shared()
        }
    }
}

pub use self::internals::RwLock;

impl RwLock {
    pub fn try_lock_exclusive_guard(&self) -> Option<LockExclusiveGuard<'_>> {
        if self.try_lock_exclusive_immediate() {
            Some(LockExclusiveGuard { lock: self })
        } else {
            None
        }
    }

    /// Try to acquire a shared lock with a guard.
    pub fn try_lock_shared(&self) -> Option<LockSharedGuard<'_>> {
        if self.try_lock_shared_immediate() {
            Some(LockSharedGuard { lock: self })
        } else {
            None
        }
    }
}

/// A lock guard for an exclusive lock.
pub struct LockExclusiveGuard<'a> {
    lock: &'a RwLock,
}

impl Drop for LockExclusiveGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_exclusive_immediate()
    }
}

/// A lock guard for a shared lock.
pub struct LockSharedGuard<'a> {
    lock: &'a RwLock,
}

impl Drop for LockSharedGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_shared_immediate()
    }
}
