//! Wake plumbing for unicycle.
//!
//! We provide two different forms of wakers:
//!
//! * `Internals` - which takes full ownership of the plumbing necessary to
//!   wake the task from another thread.

use crate::{lock::RwLock, Shared};
use std::{
    cell::UnsafeCell,
    mem, ptr,
    sync::Arc,
    task::{Context, RawWaker, RawWakerVTable, Waker},
};

/// Wrap the current context in one that updates the local WakeSet.
/// This takes the shared data by reference and reuses the `INTERNALS_VTABLE`.
///
/// It works because we don't drop the waker inside of this function.
pub(crate) fn poll_with_ref<F, R>(shared: &Arc<Shared>, index: usize, f: F) -> R
where
    F: FnOnce(&mut Context<'_>) -> R,
{
    // Need to assigned owned a fixed location, so do not move it from here for the duration of the poll.
    let internals = Internals::new(shared.clone(), index);

    let waker = RawWaker::new(&internals as *const _ as *const (), INTERNALS_VTABLE);
    let waker = mem::ManuallyDrop::new(unsafe { Waker::from_raw(waker) });
    let mut cx = Context::from_waker(&*waker);
    f(&mut cx)
}

static INTERNALS_VTABLE: &RawWakerVTable = &RawWakerVTable::new(
    Internals::clone_unchecked,
    Internals::wake_unchecked,
    Internals::wake_by_ref_unchecked,
    Internals::drop_unchecked,
);

struct Internals {
    shared: Arc<Shared>,
    index: usize,
}

impl Internals {
    /// Construct a new waker.
    fn new(shared: Arc<Shared>, index: usize) -> Self {
        Self { shared, index }
    }

    unsafe fn clone_unchecked(this: *const ()) -> RawWaker {
        // Safety: `this` is *const Self because it is called through the RawWaker vtable
        let this = &(*(this as *const Self));
        this.clone()
    }

    fn clone(&self) -> RawWaker {
        let internals = Internals::new(self.shared.clone(), self.index);
        let waker = Box::new(internals);
        RawWaker::new(Box::into_raw(waker) as *const _, INTERNALS_VTABLE)
    }

    unsafe fn wake_unchecked(this: *const ()) {
        // Safety: `this` is *const Self because it is called through the RawWaker vtable
        // Note: this will never be called when it's passed by ref.
        let this = Box::from_raw(this as *mut Self);
        this.wake()
    }

    unsafe fn wake_by_ref_unchecked(this: *const ()) {
        // Safety: `this` is *const Self because it is called through the RawWaker vtable
        let this = &(*(this as *const Self));
        this.wake()
    }

    fn wake(&self) {
        // Safety: `this` is *const Self because it is called through the RawWaker vtable
        let shared = &self.shared;
        shared.wake_set.wake(self.index);
        shared.waker.wake_by_ref();
    }

    unsafe fn drop_unchecked(this: *const ()) {
        // Safety: `this` is *const Self because it is called through the RawWaker vtable
        Box::from_raw(this as *mut Self);
    }
}

pub(crate) struct SharedWaker {
    lock: RwLock,
    waker: UnsafeCell<Waker>,
}

impl SharedWaker {
    /// Construct a new shared waker.
    pub(crate) fn new() -> Self {
        Self {
            lock: RwLock::new(),
            waker: UnsafeCell::new(noop_waker()),
        }
    }

    /// Wake the shared waker by ref.
    pub(crate) fn wake_by_ref(&self) {
        if let Some(_guard) = self.lock.try_lock_shared() {
            let waker = unsafe { &*self.waker.get() };
            waker.wake_by_ref();
        }
    }

    /// Swap out the current waker, dropping the one that was previously in
    /// place.
    ///
    /// Returns `true` if the waker was successfully swapped, or swapping is not
    /// necessary.
    ///
    /// Otherwise returns `false` and calling `wake_by_ref`, indicating that we
    /// want to try again.
    ///
    /// # Safety
    ///
    /// Caller must ensure that they are the only one who will attempt to lock
    /// the waker exclusively.
    pub(crate) unsafe fn swap(&self, waker: &Waker) -> bool {
        let shared_waker = self.waker.get();

        // Safety: No need to lock the shared waker exclusively to access an
        // immutable reference since the caller is assured to be the only one
        // trying to swap.
        if (*shared_waker).will_wake(waker) {
            return true;
        }

        if let Some(_guard) = self.lock.try_lock_exclusive_guard() {
            *self.waker.get() = waker.clone();
            return true;
        }

        waker.wake_by_ref();
        false
    }
}

/// Create a waker which does nothing.
fn noop_waker() -> Waker {
    unsafe { Waker::from_raw(noop_raw_waker()) }
}

fn noop_raw_waker() -> RawWaker {
    return RawWaker::new(
        ptr::null(),
        &RawWakerVTable::new(noop_clone, noop_wake, noop_wake_by_ref, noop_drop),
    );

    fn noop_clone(_: *const ()) -> RawWaker {
        noop_raw_waker()
    }

    fn noop_wake(_: *const ()) {}

    fn noop_wake_by_ref(_: *const ()) {}

    fn noop_drop(_: *const ()) {}
}
