use crate::lock::{LockExclusiveGuard, LockSharedGuard, RwLock};
use std::hint;
use std::sync::atomic::{AtomicPtr, Ordering};
use uniset::{AtomicBitSet, BitSet};

/// A wake set which allows us to immutably set an index.
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
    lock: RwLock,
}

impl WakeSet {
    pub(crate) fn new() -> Self {
        Self {
            set: AtomicBitSet::new(),
            lock: RwLock::new(),
        }
    }

    pub(crate) fn locked() -> Self {
        Self {
            set: AtomicBitSet::new(),
            lock: RwLock::locked(),
        }
    }

    pub(crate) fn new_raw() -> *mut Self {
        Box::into_raw(Box::new(Self::new()))
    }

    /// Try to lock the current thread until we have unique access.
    pub(crate) fn try_lock_exclusive(&self) -> bool {
        self.lock.try_lock_exclusive_immediate()
    }

    pub(crate) fn lock_exclusive(&self) {
        while !self.try_lock_exclusive() {
            hint::spin_loop();
        }
    }

    pub(crate) unsafe fn unlock_exclusive(&self) {
        self.lock.unlock_exclusive_immediate();
    }

    /// Lock interest in reading.
    pub(crate) fn try_lock_shared(&self) -> Option<LockSharedGuard<'_>> {
        self.lock.try_lock_shared()
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
    pub(crate) fn as_mut_set(&mut self) -> &mut BitSet {
        self.set.as_local_mut()
    }
}

pub(crate) struct SharedWakeSet {
    wake_set: AtomicPtr<WakeSet>,
    prevent_drop_lock: RwLock,
}

impl SharedWakeSet {
    /// Construct a new shared wake set.
    pub(crate) fn new() -> Self {
        Self {
            wake_set: AtomicPtr::new(WakeSet::new_raw()),
            prevent_drop_lock: RwLock::new(),
        }
    }

    /// Swap the current pointer with another.
    pub(crate) fn swap(&self, other: *mut WakeSet) -> *mut WakeSet {
        self.wake_set.swap(other, Ordering::AcqRel)
    }

    /// Register interesting in waking up for the specified index.
    pub(crate) fn wake(&self, index: usize) {
        // We need to spin here, since the wake set might be swapped out while we
        // are trying to update it.
        while !self.try_wake(index) {}
    }

    /// Prevent that the pointer is being written to while this guard is being
    /// held. This makes sure there are no readers in the critical section that
    /// might read an invalid wake set while it's being deallocated.
    pub(crate) fn prevent_drop_write(&self) -> LockExclusiveGuard<'_> {
        loop {
            if let Some(guard) = self.prevent_drop_lock.try_lock_exclusive_guard() {
                return guard;
            }

            hint::spin_loop();
        }
    }

    fn try_prevent_drop_read(&self) -> Option<LockSharedGuard<'_>> {
        self.prevent_drop_lock.try_lock_shared()
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

        let wake_set = self.wake_set.load(Ordering::Acquire);
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

impl Drop for SharedWakeSet {
    fn drop(&mut self) {
        let wake_set = self.wake_set.load(Ordering::Acquire);
        debug_assert!(!wake_set.is_null());

        // Safety: At this point, there are no other ways to access the
        // `SharedWakeSet`, so we are not racing against someone trying to call
        // wake. Nor are we racing against `Unordered` dropping the wake set
        // since this is the active set which has been swapped in exclusively.
        unsafe {
            drop(Box::from_raw(wake_set));
        }
    }
}
