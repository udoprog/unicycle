//! Wake plumbing for unicycle.
//!
//! We provide two different forms of wakers:
//!
//! * `Internals` - which takes full ownership of the plumbing necessary to
//!   wake the task from another thread.

use crate::{lock::RwLock, Shared};
use std::{
    cell::UnsafeCell,
    mem::{self, ManuallyDrop},
    ptr,
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
    let internals = RefWaker { shared, index };

    let waker = unsafe { Waker::from_raw(internals.as_raw_waker()) };
    let mut cx = Context::from_waker(&waker);
    f(&mut cx)
}

/// A waker that references the [Shared] waker data by reference
///
/// When cloned it converts to an [Internals] waker.
struct RefWaker<'a> {
    shared: &'a Arc<Shared>,
    index: usize,
}

impl<'a> RefWaker<'a> {
    const VTABLE: &'static RawWakerVTable = &RawWakerVTable::new(
        Self::clone,
        Self::wake_by_ref, // Use wake_by_ref for wake because RefWaker is always passed by ref
        Self::wake_by_ref,
        Self::drop,
    );

    fn clone(this: *const ()) -> RawWaker {
        // Safety: clone is called through the vtable, so we know this is a pointer to Self.
        let this = unsafe { &*(this as *const Self) };
        let internals = this.shared.get_waker(this.index);
        RawWaker::new(unsafe { mem::transmute(internals) }, INTERNALS_VTABLE)
    }

    fn wake_by_ref(this: *const ()) {
        // Safety: wake_by_ref is called through the vtable, so we know this is a pointer to Self.
        let this = unsafe { &*(this as *const Self) };
        this.shared.wake_set.wake(this.index);
        this.shared.waker.wake_by_ref();
    }

    fn drop(_: *const ()) {
        // Nothing needs to be done here because the argument is actually a &Self which will
        // be dropped by whoever owns the Self.
    }

    fn as_raw_waker(&self) -> RawWaker {
        RawWaker::new(self as *const _ as *const (), Self::VTABLE)
    }
}

static INTERNALS_VTABLE: &RawWakerVTable = &RawWakerVTable::new(
    InternalWaker::clone_unchecked,
    InternalWaker::wake_unchecked,
    InternalWaker::wake_by_ref_unchecked,
    InternalWaker::drop_unchecked,
);

pub(crate) struct InternalWaker {
    shared: *const Shared,
    pub(crate) index: usize,
}

impl InternalWaker {
    /// Construct a new waker.
    pub(crate) fn new(shared: *const Shared, index: usize) -> Self {
        Self { shared, index }
    }

    pub fn as_internal_ref(&self) -> InternalWakerRef {
        println!("Creating InternalWakerRef");
        unsafe {
            Arc::increment_strong_count(self.shared);
            InternalWakerRef(self)
        }
    }

    unsafe fn clone_unchecked(ptr: *const ()) -> RawWaker {
        let this: ManuallyDrop<InternalWakerRef> = mem::transmute(ptr);
        let internals = &*this.0;
        let internals = (*(internals.shared)).get_waker((*this.0).index);
        RawWaker::new(mem::transmute(internals), INTERNALS_VTABLE)
    }

    unsafe fn wake_by_ref_unchecked(this: *const ()) {
        let this: ManuallyDrop<InternalWakerRef> = mem::transmute(this);
        let shared = &*(*this.0).shared;
        shared.wake_set.wake((*this.0).index);
        shared.waker.wake_by_ref();
    }

    unsafe fn wake_unchecked(this: *const ()) {
        let this: InternalWakerRef = mem::transmute(this);
        let shared = &*(*this.0).shared;
        shared.wake_set.wake((*this.0).index);
        shared.waker.wake_by_ref();
    }

    unsafe fn drop_unchecked(this: *const ()) {
        let _this: InternalWakerRef = mem::transmute(this);
    }
}

#[repr(transparent)]
pub(crate) struct InternalWakerRef(*const InternalWaker);

impl Drop for InternalWakerRef {
    fn drop(&mut self) {
        println!("Dropping InternalWakerRef");
        unsafe {
            let internal = &*self.0;
            Arc::decrement_strong_count(&*internal.shared)
        }
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

#[cfg(test)]
mod test {
    use super::poll_with_ref;
    use crate::FuturesUnordered;
    use crate::Shared;
    use futures::Future;
    use std::sync::Arc;
    use std::task::{Poll, Waker};

    #[test]
    fn basic_waker() {
        let shared = Arc::new(Shared::new());
        let index = 0;

        poll_with_ref(&shared, index, |_| ())
    }

    #[test]
    fn clone_waker() {
        struct GetWaker;
        impl Future for GetWaker {
            type Output = Waker;

            fn poll(
                self: std::pin::Pin<&mut Self>,
                cx: &mut std::task::Context<'_>,
            ) -> std::task::Poll<Self::Output> {
                Poll::Ready(cx.waker().clone())
            }
        }

        block_on::block_on(async {
            let mut futures = FuturesUnordered::new();
            futures.push(GetWaker);

            futures.next().await.unwrap();
        });
    }

    #[test]
    fn long_lived_waker() {
        struct GetWaker;
        impl Future for GetWaker {
            type Output = Waker;

            fn poll(
                self: std::pin::Pin<&mut Self>,
                cx: &mut std::task::Context<'_>,
            ) -> std::task::Poll<Self::Output> {
                Poll::Ready(cx.waker().clone())
            }
        }

        let waker = block_on::block_on(async {
            let mut futures = FuturesUnordered::new();
            futures.push(GetWaker);

            futures.next().await.unwrap()
        });

        waker.wake();
    }

    mod block_on {
        //! A way to run a future to completion on the current thread.
        //!
        //! Taken from https://doc.rust-lang.org/std/task/trait.Wake.html#examples

        use futures::Future;
        use std::{
            sync::Arc,
            task::{Context, Poll, Wake},
            thread::{self, Thread},
        };

        /// A waker that wakes up the current thread when called.
        struct ThreadWaker(Thread);

        impl Wake for ThreadWaker {
            fn wake(self: Arc<Self>) {
                self.0.unpark();
            }
        }

        /// Run a future to completion on the current thread.
        pub(super) fn block_on<T>(fut: impl Future<Output = T>) -> T {
            // Pin the future so it can be polled.
            let mut fut = Box::pin(fut);

            // Create a new context to be passed to the future.
            let t = thread::current();
            let waker = Arc::new(ThreadWaker(t)).into();
            let mut cx = Context::from_waker(&waker);

            // Run the future to completion.
            loop {
                match fut.as_mut().poll(&mut cx) {
                    Poll::Ready(res) => return res,
                    Poll::Pending => thread::park(),
                }
            }
        }
    }
}
