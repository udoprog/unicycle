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
    let internals = Internals::new(&**shared as *const Shared, index);

    let waker = RawWaker::new(&internals as *const _ as *const (), INTERNALS_VTABLE);
    let waker = mem::ManuallyDrop::new(unsafe { Waker::from_raw(waker) });
    let mut cx = Context::from_waker(&*waker);
    f(&mut cx)
}

static INTERNALS_VTABLE: &RawWakerVTable = &RawWakerVTable::new(
    Internals::clone,
    Internals::wake,
    Internals::wake_by_ref,
    Internals::drop,
);

struct Internals {
    shared: *const Shared,
    index: usize,
}

impl Internals {
    /// Construct a new waker.
    fn new(shared: *const Shared, index: usize) -> Self {
        Self { shared, index }
    }

    unsafe fn clone(this: *const ()) -> RawWaker {
        let this = &(*(this as *const Self));
        let s1 = mem::ManuallyDrop::new(Arc::from_raw(this.shared));
        #[allow(clippy::redundant_clone)]
        let s2 = s1.clone();
        let index = this.index;
        let waker = Box::into_raw(Box::new(Internals::new(&**s2 as *const Shared, index)));
        RawWaker::new(waker as *const (), INTERNALS_VTABLE)
    }

    unsafe fn wake(this: *const ()) {
        // Note: this will never be called when it's passed by ref.
        let this = Box::from_raw(this as *mut Self);
        let shared = &(*this.shared);
        shared.wake_set.wake(this.index);
        shared.waker.wake_by_ref();
        drop(Arc::from_raw(this.shared));
    }

    unsafe fn wake_by_ref(this: *const ()) {
        let this = &(*(this as *const Self));
        let shared = &(*this.shared);
        shared.wake_set.wake(this.index);
        shared.waker.wake_by_ref();
    }

    unsafe fn drop(this: *const ()) {
        let this = Box::from_raw(this as *mut Self);
        drop(Arc::from_raw(this.shared));
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

    unsafe fn noop_clone(_: *const ()) -> RawWaker {
        noop_raw_waker()
    }

    unsafe fn noop_wake(_: *const ()) {}

    unsafe fn noop_wake_by_ref(_: *const ()) {}

    unsafe fn noop_drop(_: *const ()) {}
}
