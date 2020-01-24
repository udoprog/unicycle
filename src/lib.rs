#![deny(missing_docs)]
//! A container for an unordered collection of [Future]s.
//! This provides an experimental variant of `FuturesUnordered` aimed to be
//! _fairer_. Easier to maintain, and store the futures being polled in a way which
//! provides better memory locality.
//!
//! ## Architecture
//!
//! The `Unordered` type stores all futures being polled in a `PinSlab`. This [slab]
//! maintains a growable collection of fixed-size memory regions, allowing it to
//! store immovable objects. The primary feature of a slab is that it automatically
//! reclaims memory at low cost. Each future inserted into the slab is asigned an
//! _index_.
//!
//! Next to the futures we maintain two bitsets, one _active_ and one
//! _alternate_. When a future is woken up, the bit associated with its index is
//! set in the _active_ set, and the waker associated with the poll to `Unordered`
//! is called.
//!
//! Once `Unordered` is polled, it atomically swaps the _active_ and _alternate_
//! bitsets, waits until it has exclusive access to the now _alternate_ bitset, and
//! drains it from all the indexes which have been flagged to determine which
//! futures to poll.
//!
//! We can also add futures to `Unordered`, this is achieved by inserting it into
//! the slab, then marking that index in a special `pollable` collection that it
//! should be polled the next time `Unordered` is.
//!
//! [slab]: https://github.com/carllerche/slab
//!
//! ## Examples
//!
//! ```rust,no_run
//! use tokio::{stream::StreamExt as _, time};
//! use std::time::Duration;
//!
//! #[tokio::main]
//! async fn main() {
//!     let mut futures = unicycle::Unordered::new();
//!
//!     futures.push(time::delay_for(Duration::from_secs(2)));
//!     futures.push(time::delay_for(Duration::from_secs(3)));
//!     futures.push(time::delay_for(Duration::from_secs(1)));
//!
//!     while let Some(_) = futures.next().await {
//!         println!("tick");
//!     }
//!
//!     println!("done!");
//! }
//! ```

use self::pin_slab::PinSlab;
use self::wake_set::{SharedWakeSet, WakeSet};
use futures_core::Stream;
use std::{
    collections::VecDeque,
    future::Future,
    iter, mem,
    pin::Pin,
    ptr,
    sync::Arc,
    task::{Context, Poll, RawWaker, Waker},
};

mod pin_slab;
mod wake_set;
mod waker;

/// A container for an unordered collection of [Future]s.
pub struct Unordered<F>
where
    F: Future,
{
    // Indexes that needs to be polled after they have been added.
    pollable: Vec<usize>,
    // Slab of futures being polled.
    // They need to be pinned on the heap, since the slab might grow to
    // accomodate more futures.
    slab: PinSlab<F>,
    // The current wake target. Each time we poll, we swap back and forth
    // between this and `wake_alternate`.
    wake_current: Arc<SharedWakeSet>,
    // Alternate wake set, used for growing the existing set when futures are
    // added. This is then swapped out with the active set to receive polls.
    wake_alternate: *mut WakeSet,
    // Pending outgoing results. Uses a queue to avoid interrupting polling.
    results: VecDeque<F::Output>,
}

impl<F> Unpin for Unordered<F> where F: Future {}

impl<F> Unordered<F>
where
    F: Future,
{
    /// Construct a new, empty [Unordered].
    pub fn new() -> Self {
        let alternate = WakeSet::new();
        alternate.lock_write();

        Self {
            pollable: Vec::with_capacity(16),
            slab: PinSlab::new(),
            wake_current: Arc::new(SharedWakeSet::new()),
            wake_alternate: Box::into_raw(Box::new(alternate)),
            results: VecDeque::new(),
        }
    }

    /// Add the given future to the [Unordered] stream.
    pub fn push(&mut self, future: F) {
        let index = self.slab.insert(future);
        self.pollable.push(index);
    }
}

impl<F> Drop for Unordered<F>
where
    F: Future,
{
    fn drop(&mut self) {
        // Safety: we uniquely own `wake_alternate`, so we are responsible for
        // dropping it. This is asserted when we swap it out during a poll by
        // calling WakeSet::wait_for_unique_access. We are also the _only_ one
        // swapping `wake_alternative`, so we know that can't happen here.
        unsafe {
            WakeSet::drop_raw(self.wake_alternate);
        }
    }
}

impl<F> Stream for Unordered<F>
where
    F: Unpin + Future,
{
    type Item = F::Output;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let Self {
            ref mut pollable,
            ref mut results,
            ref mut slab,
            ref wake_current,
            ref mut wake_alternate,
            ..
        } = *self.as_mut();

        loop {
            if let Some(value) = results.pop_front() {
                cx.waker().wake_by_ref();
                return Poll::Ready(Some(value));
            }

            if slab.is_empty() {
                // Nothing to poll, nothing to add. And the stream since we
                // don't have more work to do.
                return Poll::Ready(None);
            }

            let wake_last = {
                unsafe {
                    (**wake_alternate).unlock_write();
                }

                let next = mem::replace(wake_alternate, ptr::null_mut());
                *wake_alternate = wake_current.swap(next);

                // Make sure no one else is using the alternate wake.
                //
                // Safety: We are the only one swapping wake_alternate, so at
                // this point we know that we have access to the most recent
                // active set. We _must_ call wait_for_unique_access before we
                // can punt this into a mutable reference though, because at
                // this point inner futures will still have access to references
                // to it (under a lock!). We must wait for these to expire.
                unsafe {
                    (**wake_alternate).lock_write();
                    &mut **wake_alternate
                }
            };

            let indexes = iter::from_fn(|| pollable.pop()).chain(wake_last.drain());

            for index in indexes {
                // NB: Since we defer pollables a little, a future might
                // have been polled and subsequently removed from the slab.
                // So we don't treat this as an error here.
                // If on the other hand it was removed _and_ re-added, we have
                // a case of a spurious poll. Luckily, that doesn't bother a
                // future much.
                let fut = match slab.get_pin_mut(index) {
                    Some(fut) => fut,
                    None => continue,
                };

                // Construct a new lightweight waker only capable of waking by
                // reference, with referential access to `wake_current` and parent.
                // In order to store this waker, it must be cloned.
                let result = ref_poll(cx, wake_current, index, move |cx| fut.poll(cx));

                if let Poll::Ready(result) = result {
                    results.push_back(result);
                    let removed = slab.remove(index);
                    debug_assert!(removed);
                }
            }

            // break if we don't have any additional work to do.
            if results.is_empty() {
                break;
            }
        }

        Poll::Pending
    }
}

/// Wrap the current context in one that updates the local WakeSet when woken.
fn ref_poll<F, R>(cx: &mut Context<'_>, wake_current: &Arc<SharedWakeSet>, index: usize, f: F) -> R
where
    F: FnOnce(&mut Context<'_>) -> R,
{
    let waker = self::waker::WakerRef::new(cx.waker(), wake_current, index);
    let waker = RawWaker::new(
        &waker as *const _ as *const (),
        self::waker::WAKER_REF_VTABLE,
    );
    let waker = unsafe { Waker::from_raw(waker) };
    let mut cx = Context::from_waker(&waker);
    f(&mut cx)
}
