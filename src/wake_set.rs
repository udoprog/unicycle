use crate::bit_set::{AtomicBitSet, BitSet};
use lock_api::RawRwLock;
use std::sync::atomic::{AtomicPtr, Ordering};

/// A wake set which allows us to immutably set an index.
#[repr(C)]
pub(crate) struct WakeSet {
    set: AtomicBitSet,
    /// Read locks are held every time someone manipulates the underlying set,
    /// we then (briefly) acquire a write lock to get unique access, after we
    /// have swapped out the wake set pointer.
    ///
    /// We keep this lock separate since we operate over raw pointers, and we'd
    /// like the ability to "shed" the lock from `LocalWakeSet` when
    /// appropriate. I.e. we don't want to keep track of a lock guard, but we
    /// still have a region of operation where we want to consider the wake set
    /// as exclusively owned.
    lock: parking_lot::RawRwLock,
}

/// The same wake set as above, but with a local bitset that can be mutated.
#[repr(C)]
pub(crate) struct LocalWakeSet {
    pub(crate) set: BitSet,
    _lock: parking_lot::RawRwLock,
}

impl WakeSet {
    pub(crate) fn new() -> Self {
        Self {
            set: AtomicBitSet::new(),
            lock: parking_lot::RawRwLock::INIT,
        }
    }

    pub(crate) fn new_raw() -> *mut Self {
        Box::into_raw(Box::new(Self::new()))
    }

    /// Blocks the current thread until we have unique access.
    ///
    /// This should be for a very short period of time.
    pub(crate) fn lock_exclusive(&self) {
        self.lock.lock_exclusive()
    }

    pub(crate) fn unlock_exclusive(&self) {
        self.lock.unlock_exclusive()
    }

    /// Lock interest in reading.
    pub(crate) fn try_lock_shared(&self) -> Option<SharedLockGuard<'_>> {
        if !self.lock.try_lock_shared() {
            return None;
        }

        Some(SharedLockGuard { lock: &self.lock })
    }

    /// Drop a wake set through a pointer.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the dropped pointer is valid.
    pub(crate) unsafe fn drop_raw(this: *mut Self) {
        drop(Box::from_raw(this))
    }

    /// Set the given index in the referenced bitset.
    pub(crate) fn set(&self, index: usize) {
        self.set.set(index);
    }

    /// Treat the bitset as a local, mutable BitSet.
    ///
    /// Caller must ensure that they have unique access to the atomic bit set by
    /// only using this while an exclusive lock is held through
    /// `lock_exclusive`.
    pub(crate) fn as_local_mut(&mut self) -> &mut LocalWakeSet {
        // Safety: `LocalWakeSet` has the same memory layout as `WakeSet`: It
        // has the same memory layout as the other set, since `AtomicBitSet` is
        // guaranteed to have the same layout as `BitSet`.
        unsafe { &mut *(self as *mut _ as *mut LocalWakeSet) }
    }
}

pub(crate) struct SharedLockGuard<'a> {
    lock: &'a parking_lot::RawRwLock,
}

impl Drop for SharedLockGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_shared()
    }
}

pub(crate) struct SharedWakeSet {
    wake_set: AtomicPtr<WakeSet>,
    prevent_drop_lock: parking_lot::RawRwLock,
}

impl SharedWakeSet {
    /// Construct a new shared wake set.
    pub(crate) fn new() -> Self {
        Self {
            wake_set: AtomicPtr::new(WakeSet::new_raw()),
            prevent_drop_lock: parking_lot::RawRwLock::INIT,
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

    /// Register wakeup for the specified index.
    pub(crate) fn wake(&self, index: usize) {
        // We need to spin here, since the wake set might be swapped out while we
        // are trying to update it.
        while !self.try_wake(index) {}
    }

    /// Prevent that the pointer is being written to while this guard is being
    /// held. This makes sure there are no readers in the critical section that
    /// might read an invalid wake set while it's being deallocated.
    pub(crate) fn prevent_drop_write(&self) -> PreventDropWriteGuard<'_> {
        self.prevent_drop_lock.lock_exclusive();

        PreventDropWriteGuard {
            lock: &self.prevent_drop_lock,
        }
    }

    fn try_prevent_drop_read(&self) -> Option<PreventDropReadGuard<'_>> {
        if !self.prevent_drop_lock.try_lock_shared() {
            return None;
        }

        Some(PreventDropReadGuard {
            lock: &self.prevent_drop_lock,
        })
    }

    fn try_wake(&self, index: usize) -> bool {
        // Here is a critical section that becomes relevant if we are trying to
        // drop the unordered set.
        //
        // This prevents the unordered set from being dropped while we hold this
        // guard, which means that the pointer we read must always point to
        // allocated memory. Otherwise a reader might get past the point that we
        // loaded the pointer from `self`, but before we tried to acquire the
        // read guard and set the index _while_ the active wake set is being
        // dropped.
        let _guard = match self.try_prevent_drop_read() {
            Some(guard) => guard,
            None => return false,
        };

        let wake_set = self.load();
        debug_assert!(!wake_set.is_null());

        // Safety: We know wake_set references valid memory, because in order to
        // have access to `SharedWakeSet`, we must also hold an `Arc` to it - either
        // through a reference or by it being stored in `Internals`.
        //
        // There is however a short window in which the wake set has been swapped in
        // `Unordered`, but at this point it is not possible for it to be
        // invalidated. This can only happen if `Unordered` is dropped, and this
        // does not happen while it's being polled.
        let wake_set = unsafe { &*wake_set };

        let _guard2 = match wake_set.try_lock_shared() {
            Some(guard) => guard,
            None => return false,
        };

        wake_set.set(index);
        true
    }
}

struct PreventDropReadGuard<'a> {
    lock: &'a parking_lot::RawRwLock,
}

impl Drop for PreventDropReadGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_shared();
    }
}

pub(crate) struct PreventDropWriteGuard<'a> {
    lock: &'a parking_lot::RawRwLock,
}

impl Drop for PreventDropWriteGuard<'_> {
    fn drop(&mut self) {
        self.lock.unlock_exclusive();
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
