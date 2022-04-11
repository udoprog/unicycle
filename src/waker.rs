//! Wake plumbing for unicycle.
//!
//! We provide two different forms of wakers:
//!
//! * Stack allocated - A lightweight waker stored on the stack that converts into a waker owned
//!   by a [Shared] when cloned.
//! * [Shared]-owned [InternalWaker] - Takes full ownership of the plumbing necessary to
//!   wake the task from another thread. These must be stored in an [InternalWakers] collection
//!   that is owned by a [Shared] task structure.

#![warn(clippy::undocumented_unsafe_blocks)]

use crate::{lock::RwLock, pin_vec::PinVec, Shared};
use std::{
    cell::UnsafeCell,
    mem::{self, ManuallyDrop},
    ptr::{self, NonNull},
    sync::Arc,
    task::{Context, RawWaker, RawWakerVTable, Waker},
};

/// Wrap the current context in one that updates the local WakeSet.
/// This takes the shared data by reference and uses `RefWaker::VTABLE`.
///
/// It works because we don't drop the waker inside of this function.
pub(crate) fn poll_with_ref<F, R>(shared: &Arc<Shared>, index: usize, f: F) -> R
where
    F: FnOnce(&mut Context<'_>) -> R,
{
    // Need to assigned owned a fixed location, so do not move it from here for the duration of the poll.
    let internals =
        InternalWaker::new_on_stack(NonNull::new(Arc::as_ptr(shared) as *mut _).unwrap(), index);

    // Safety: as_raw_waker() returns an object that upholds the right RawWaker contract.
    let waker = unsafe { Waker::from_raw(internals.as_internal_ref().into()) };
    let mut cx = Context::from_waker(&waker);
    f(&mut cx)
}

/// A collection of [InternalWaker]s owned by a [Shared] task structure.
pub(crate) struct InternalWakers {
    wakers: parking_lot::Mutex<PinVec<InternalWaker>>,
}

impl InternalWakers {
    pub fn new() -> Self {
        Self {
            wakers: parking_lot::Mutex::new(PinVec::new()),
        }
    }
}

struct InternalWaker {
    /// A pointer to the [Shared] task data.
    ///
    /// This is actually an Arc, so it's possible to do increment_strong_count and
    /// decrement_strong_count on it.
    ///
    /// Note that the [InternalWaker] itself doesn't have a strong reference to [Shared], because
    /// the [InternalWaker] is assumed to be contained in the [Shared] via [InternalWakers]. Using
    /// a strong reference would create a cycle leading to the [Shared] and all its wakers leaking.
    ///
    /// Instead, we increment and decrement the ref count on [Shared] when creating and dropping
    /// an [InternalWakerRef] that refers to this waker. This is done so that cloning an
    /// [InternalWaker] (technically cloning an [InternalWakerRef]) can be done without any new
    /// heap allocations.
    shared: NonNull<Shared>,
    /// The index of the task this waker will wake.
    index: usize,
    /// Indicates whether references to this waker need to be dropped.
    ///
    /// This is primarily a way to distinguished [InternalWakers]s stored on the stack from
    /// those stored in an [InternalWakers] collection. The references to wakers in
    /// [InternalWakers] increment the ref count on the `Arc<Shared>` holding them, so the ref
    /// count needs to be decremented when the reference is destroyed.
    needs_drop: bool,
}

impl InternalWaker {
    /// Construct a new waker.
    fn new(shared: NonNull<Shared>, index: usize) -> Self {
        Self {
            shared,
            index,
            needs_drop: true,
        }
    }

    /// Constructs a new waker that is stored on the stack, and therefore references
    /// to it should not manipulate the ref count.
    fn new_on_stack(shared: NonNull<Shared>, index: usize) -> Self {
        Self {
            shared,
            index,
            needs_drop: false,
        }
    }

    fn as_internal_ref(&self) -> InternalWakerRef {
        InternalWakerRef::from_waker(self)
    }

    fn shared(&self) -> &Shared {
        // Safety: self.shared is known to point to a valid Shared by construction
        unsafe { self.shared.as_ref() }
    }
}

#[repr(transparent)]
struct InternalWakerRef(*const InternalWaker);

impl InternalWakerRef {
    fn get_shared_waker(shared: &Shared, index: usize) -> Self {
        let mut all_wakers = shared.all_wakers.wakers.lock();
        if all_wakers.len() <= index {
            let len = all_wakers.len();
            all_wakers.extend((len..index + 1).map(|i| InternalWaker::new(shared.into(), i)));
        }

        all_wakers[index].as_internal_ref()
    }

    fn from_waker(waker: &InternalWaker) -> Self {
        if waker.needs_drop {
            // Safety: self.shared is an Arc, and this will be decremented again int
            // InternalWakerRef::drop.
            unsafe {
                Arc::increment_strong_count(waker.shared.as_ptr());
            }
        }
        InternalWakerRef(waker)
    }

    fn internals(&self) -> &InternalWaker {
        // Safety: InternalWakerRef points to an InternalWaker by construction
        unsafe { &*self.0 }
    }

    const VTABLE: &'static RawWakerVTable = &RawWakerVTable::new(
        Self::clone_unchecked,
        Self::wake_unchecked,
        Self::wake_by_ref_unchecked,
        Self::drop_unchecked,
    );

    unsafe fn clone_unchecked(ptr: *const ()) -> RawWaker {
        let this: ManuallyDrop<InternalWakerRef> = mem::transmute(ptr);
        if this.internals().needs_drop {
            Arc::increment_strong_count(this.internals().shared.as_ptr());
            RawWaker::new(ptr, Self::VTABLE)
        } else {
            InternalWakerRef::get_shared_waker(
                &*(this.internals().shared.as_ptr()),
                this.internals().index,
            )
            .into()
        }
    }

    unsafe fn wake_by_ref_unchecked(this: *const ()) {
        let this: ManuallyDrop<InternalWakerRef> = mem::transmute(this);
        let internals = this.internals();
        internals.shared().wake_set.wake(internals.index);
        internals.shared().waker.wake_by_ref();
    }

    unsafe fn wake_unchecked(this: *const ()) {
        let this: InternalWakerRef = mem::transmute(this);
        let internals = this.internals();
        internals.shared().wake_set.wake(internals.index);
        internals.shared().waker.wake_by_ref();
    }

    unsafe fn drop_unchecked(this: *const ()) {
        let _this: InternalWakerRef = mem::transmute(this);
    }
}

impl From<InternalWakerRef> for RawWaker {
    fn from(val: InternalWakerRef) -> Self {
        let waker = RawWaker::new(val.0 as *const _, InternalWakerRef::VTABLE);
        mem::forget(val); // val will be dropped from RawWaker's vtable
        waker
    }
}

impl Drop for InternalWakerRef {
    fn drop(&mut self) {
        if self.internals().needs_drop {
            // Safety: internals.shared is actually an Arc<Shared>. The ref count was incremented
            // when self was constructed, so now we clean it up
            unsafe { Arc::decrement_strong_count(self.internals().shared.as_ptr()) }
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
            // Safety: We can access the unsafe cell because we are holding the lock
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
    // Safety: noop_raw_waker() returns an object that upholds the right RawWaker contract.
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
    use futures::future::poll_fn;
    use futures::Future;
    use std::cell::RefCell;
    use std::mem;
    use std::pin::Pin;
    use std::rc::Rc;
    use std::sync::Arc;
    use std::task::Context;
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

    #[test]
    fn many_wakers() {
        // This test primarily makes sure that the array of Wakers stays pinned
        // as more wakers are added.

        block_on::block_on(async {
            let mut futures = FuturesUnordered::new();

            let wake1 = Rc::new(RefCell::new(None));
            let wake2: Rc<RefCell<Option<Waker>>> = Rc::new(RefCell::new(None));
            let woken = Rc::new(RefCell::new(false));

            {
                let woken = woken.clone();
                let wake1 = wake1.clone();
                let wake2 = wake2.clone();
                futures.push(FakeDynFuture::new(poll_fn(move |cx| {
                    if *woken.borrow() {
                        // We've been awoken, so complete
                        Poll::Ready(())
                    } else {
                        if wake1.borrow().is_none() {
                            *wake1.borrow_mut() = Some(cx.waker().clone());
                        }
                        // Wake the other future if somehow it ran before us.
                        if let Some(waker) = wake2.borrow().as_ref() {
                            waker.wake_by_ref()
                        }
                        Poll::Pending
                    }
                })));
            }

            // Poll our future once to be sure to clone the waker
            poll_fn(|cx| {
                assert_eq!(
                    crate::PollNext::poll_next(Pin::new(&mut futures), cx),
                    Poll::Pending
                );
                Poll::Ready(())
            })
            .await;

            // Push a bunch of do-nothing futures to force the underlying waker table to resize.
            //
            // We do 127 of them because that the smallest number that fails in miri and segfaults
            // natively.
            for _ in 0..127 {
                futures.push(FakeDynFuture::new(poll_fn(|cx| {
                    // clone the waker to force the table to fill in.
                    let _ = cx.waker().clone();
                    Poll::Ready(())
                })));
            }

            // Now push a future that wakes the first one
            futures.push(FakeDynFuture::new(poll_fn(move |cx| {
                match &*wake1.borrow() {
                    Some(waker) => {
                        *woken.borrow_mut() = true;
                        waker.wake_by_ref();
                        Poll::Ready(())
                    }
                    None => {
                        // the other future hasn't run yet, so add our waker and then return pending.
                        *wake2.borrow_mut() = Some(cx.waker().clone());
                        Poll::Pending
                    }
                }
            })));

            while futures.next().await.is_some() {}
        })
    }

    /// Miri can't handle the vtables we ended up with originally, so this is a manual version
    /// that should work better with miri.
    struct FakeDynFuture<T> {
        future: *const (),
        poll_fn: fn(this: *const (), cx: &mut Context) -> Poll<T>,
        drop_fn: fn(this: *const ()),
    }

    impl<T> FakeDynFuture<T> {
        fn new<F: Future<Output = T>>(fut: F) -> Self {
            Self {
                future: Box::into_raw(Box::new(fut)) as *const _,
                poll_fn: |this, cx| {
                    // Safety: this is self.future (see the poll implementation below), which
                    // is a Box<F>. Boxes never move, so we can treat it as a pinned reference.
                    let this = unsafe { mem::transmute::<_, Pin<&mut F>>(this) };
                    this.poll(cx)
                },
                drop_fn: |this| {
                    // Safety: this is self.future (see the drop implementation below), which is a
                    // Box<F>.
                    unsafe {
                        mem::transmute::<_, Pin<Box<F>>>(this);
                    }
                },
            }
        }
    }

    impl<T> Future for FakeDynFuture<T> {
        type Output = T;

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            (self.poll_fn)(self.future, cx)
        }
    }

    impl<T> Drop for FakeDynFuture<T> {
        fn drop(&mut self) {
            (self.drop_fn)(self.future)
        }
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
