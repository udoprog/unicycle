//! Wake plumbing for unicycle.
//!
//! We provide two different forms of wakers:
//!
//! * `WakerRef` - which uses local references, and therefore can _only_ wake
//!   things by reference.
//! * `WakerOwned` - which takes full ownership of the plumbing necessary to
//!   wake the task from another thread.

use crate::{wake_set::SharedWakeSet, Shared};
use std::{
    ptr,
    sync::{
        atomic::{AtomicPtr, Ordering},
        Arc,
    },
    task::{RawWaker, RawWakerVTable, Waker},
};

fn try_wake(wake_set: &SharedWakeSet, index: usize) -> bool {
    let wake_set = wake_set.load();
    debug_assert!(!wake_set.is_null());

    // Safety: We know wake_set references valid memory, because in order to
    // have access to `SharedWakeSet`, we must also hold an `Arc` to it - either
    // through a reference or by it being stored in `WakerOwned`.
    //
    // There is however a short window in which the wake set has been swapped in
    // `Unordered`, but at this point it is not possible for it to be
    // invalidated. This can only happen if `Unordered` is dropped, and this
    // does not happen while it's being polled.
    let wake_set = unsafe { &*wake_set };

    if let Some(_guard) = wake_set.try_read_lock() {
        wake_set.set(index);
        true
    } else {
        false
    }
}

/// Register wakeup in the [WakeSet].
fn wake(wake_set: &SharedWakeSet, index: usize) {
    // We need to spin here, since the wake set might be swapped out while we
    // are trying to update it.
    while !try_wake(wake_set, index) {}
}

pub(crate) struct WakerRef {
    shared: *const Arc<Shared>,
    index: usize,
}

impl WakerRef {
    /// Construct a new WakerRef.
    pub(crate) fn new(shared: *const Arc<Shared>, index: usize) -> Self {
        Self { shared, index }
    }

    unsafe fn clone(this: *const ()) -> RawWaker {
        let this = &(*(this as *const Self));
        let shared = (*this.shared).clone();
        let index = this.index;
        let waker = Box::into_raw(Box::new(WakerOwned::new(shared, index)));
        RawWaker::new(waker as *const (), WAKER_OWNED_VTABLE)
    }

    unsafe fn wake(_: *const ()) {
        unreachable!();
    }

    unsafe fn wake_by_ref(this: *const ()) {
        let this = &(*(this as *const Self));
        wake(&(*this.shared).wake_set, this.index);
        (*this.shared).waker.wake_by_ref();
    }

    unsafe fn drop(_: *const ()) {
        // NB: everything is held by reference, so no need to drop.
    }
}

pub(crate) static WAKER_REF_VTABLE: &RawWakerVTable = &RawWakerVTable::new(
    WakerRef::clone,
    WakerRef::wake,
    WakerRef::wake_by_ref,
    WakerRef::drop,
);

pub(crate) struct WakerOwned {
    shared: Arc<Shared>,
    index: usize,
}

impl WakerOwned {
    /// Construct a new WakerRef.
    pub(crate) fn new(shared: Arc<Shared>, index: usize) -> Self {
        Self { shared, index }
    }

    unsafe fn clone(this: *const ()) -> RawWaker {
        let this = &(*(this as *const Self));
        let shared = this.shared.clone();
        let index = this.index;
        let waker = Box::into_raw(Box::new(WakerOwned::new(shared, index)));
        RawWaker::new(waker as *const (), WAKER_OWNED_VTABLE)
    }

    unsafe fn wake(this: *const ()) {
        let this = Box::from_raw(this as *mut Self);
        wake(&this.shared.wake_set, this.index);
        this.shared.waker.wake_by_ref();
    }

    unsafe fn wake_by_ref(this: *const ()) {
        let this = &(*(this as *const Self));
        wake(&this.shared.wake_set, this.index);
        this.shared.waker.wake_by_ref();
    }

    unsafe fn drop(this: *const ()) {
        // NB: all references, nothing to drop.
        drop(Box::from_raw(this as *mut Self));
    }
}

pub(crate) static WAKER_OWNED_VTABLE: &RawWakerVTable = &RawWakerVTable::new(
    WakerOwned::clone,
    WakerOwned::wake,
    WakerOwned::wake_by_ref,
    WakerOwned::drop,
);

pub(crate) struct SharedWaker {
    waker: AtomicPtr<Waker>,
}

impl SharedWaker {
    /// Construct a new shared waker.
    pub(crate) fn new() -> Self {
        Self {
            waker: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Wake the shared waker by ref.
    pub(crate) fn wake_by_ref(&self) {
        let waker = self.waker.load(Ordering::Acquire);

        if !waker.is_null() {
            let waker = unsafe { &*waker };
            waker.wake_by_ref();
        }
    }

    /// Test if the current waker will wake another waker.
    pub(crate) fn is_woken_by(&self, other: &Waker) -> bool {
        let current = self.waker.load(Ordering::Acquire);

        if current.is_null() {
            return false;
        }

        // Safety: we are the only one managing the state of the current waker.
        // If non-null, it is correctly initialized.
        let current = unsafe { &*current };
        other.will_wake(current)
    }

    /// Swap out the current waker, dropping the one that was previously in
    /// place.
    pub(crate) fn swap(&self, waker: Waker) {
        let waker = Box::into_raw(Box::new(waker));
        let old = self.waker.swap(waker, Ordering::AcqRel);

        if !old.is_null() {
            // Safety: we are the only one managing the state of the current waker.
            // If non-null, it is correctly initialized.
            drop(unsafe { Box::from_raw(old) });
        }
    }
}

impl Drop for SharedWaker {
    fn drop(&mut self) {
        // Note: no need to swap here since this is at the end of the
        // SharedWaker.
        let old = self.waker.load(Ordering::Acquire);

        if !old.is_null() {
            // Safety: we are the only one managing the state of the current waker.
            // If non-null, it is correctly initialized.
            drop(unsafe { Box::from_raw(old) });
        }
    }
}
