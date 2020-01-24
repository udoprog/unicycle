use lock_api::RawRwLock;
use std::sync::atomic::{AtomicPtr, Ordering};

/// A wake set which allows us to immutably set an index.
pub(crate) struct WakeSet {
    set: hibitset::AtomicBitSet,
    /// Read locks are held every time someone manipulates the underlying set,
    /// we then (briefly) acquire a write lock to get unique access, after we
    /// have swapped out the wake set pointer.
    ///
    /// We keep this lock separate since we operate over raw pointers.
    lock: parking_lot::RawRwLock,
}

impl WakeSet {
    pub(crate) fn new() -> Self {
        Self {
            set: hibitset::AtomicBitSet::new(),
            lock: parking_lot::RawRwLock::INIT,
        }
    }

    pub(crate) fn new_raw() -> *mut Self {
        Box::into_raw(Box::new(Self::new()))
    }

    /// Blocks the current thread until we have unique access.
    ///
    /// This should be for a very short period of time.
    pub(crate) fn lock_write(&self) {
        self.lock.lock_exclusive()
    }

    pub(crate) fn unlock_write(&self) {
        self.lock.unlock_exclusive()
    }

    /// Lock interest in reading.
    pub(crate) fn try_read_lock(&self) -> Option<ReadLockGuard<'_>> {
        if !self.lock.try_lock_shared() {
            return None;
        }

        Some(ReadLockGuard { lock: &self.lock })
    }

    /// Drop a wake set through a pointer.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the dropped pointer is valid.
    pub(crate) unsafe fn drop_raw(this: *mut Self) {
        drop(Box::from_raw(this))
    }

    /// Set the given index in the bitset.
    pub(crate) fn set(&self, index: usize) {
        self.set.add_atomic(index as u32);
    }

    /// Create a draining iterator of the current wake set.
    ///
    /// Having an index return from the draining iterator will cause it to be
    /// removed from the underlying WakeSet.
    pub(crate) fn drain(&mut self) -> impl Iterator<Item = usize> + '_ {
        use hibitset::DrainableBitSet;
        self.set.drain().map(|i| i as usize)
    }
}

pub(crate) struct ReadLockGuard<'a> {
    lock: &'a parking_lot::RawRwLock,
}

impl Drop for ReadLockGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_shared()
    }
}

pub(crate) struct SharedWakeSet {
    wake_set: AtomicPtr<WakeSet>,
}

impl SharedWakeSet {
    /// Construct a new shared wake set.
    pub(crate) fn new() -> Self {
        Self {
            wake_set: AtomicPtr::new(WakeSet::new_raw()),
        }
    }

    /// Swap the current pointer with another.
    pub(crate) fn swap(&self, other: *mut WakeSet) -> *mut WakeSet {
        self.wake_set.swap(other, Ordering::AcqRel)
    }

    /// Load the current wake set.
    pub(crate) fn load(&self) -> *const WakeSet {
        self.wake_set.load(Ordering::Acquire)
    }
}

impl Drop for SharedWakeSet {
    fn drop(&mut self) {
        let wake_set = self.wake_set.load(Ordering::Acquire);
        assert!(!wake_set.is_null());
        unsafe {
            WakeSet::drop_raw(wake_set);
        }
    }
}
