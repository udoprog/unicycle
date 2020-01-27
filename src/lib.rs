#![deny(missing_docs)]
#![allow(clippy::needless_doctest_main)]
//! Unicycle aims to provide a futures abstraction that runs a set of futures which
//! may complete in any order. Similarly to [`FuturesUnordered`]. But we aim to
//! provide a stronger guarantee of fairness (see below), and better memory locality
//! for the futures being pollled.
//!
//! [`FuturesUnordered`]: https://docs.rs/futures/latest/futures/stream/struct.FuturesUnordered.html
//!
//! **Note:** This project is experimental. It involves some amount of unsafe and
//! possibly bad assumptions which needs to be either vetted or removed before you
//! should consider putting it in production.
//!
//! ## Features
//!
//! * `parking-lot` - To enable locking using the [parking_lot] crate (optional).
//!
//! [parking_lot]: https://crates.io/crates/parking_lot
//!
//! ## Examples
//!
//! ```rust
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
//!
//! ## Fairness
//!
//! You can think of abstractions like Unicycle as schedulers. They are provided a
//! set of child tasks, and try to do their best to drive them to completion. In
//! this regard, it's interesting to talk about _fairness_ in how the tasks are
//! being driven - in the same degree as we talk about fairness in other forms of
//! scheduling.
//!
//! The current implementation of `FuturesUnordered` maintains a queue of tasks
//! interested in waking up. As a task is woken up, it's added to the head of this
//! queue to signal it's interest. When `FuturesUnordered` is being polled, it
//! checks the head of this queue in a loop. As long as there is a task interested
//! in being woken up, this task will be polled. This procuedure has the side effect
//! of tasks which aggressively signal interest in waking up will receive priority,
//! and be polled more frequently.
//!
//! This process can lead to an especially unfortunate cases where a small number of
//! task can can cause the polling loop of `FuturesUnordered` to [spin abnormally].
//! This issue was [reported by Jon Gjengset].
//!
//! Unicycle addresses this by limiting how frequently a child task may be polled
//! per _polling cycle_. This is done by keeping two sets of polling interest and
//! atomically swapping it out once we are polling, then taking the swapped out set
//! and use as a basis for what to poll in order, but only _once_. Additional
//! wakeups are only registered in the swapped in set which will be polled the next
//! cycle. For more details, see the _Architecture_ section below.
//!
//! [spin abnormally]: https://github.com/udoprog/unicycle/blob/master/tests/spinning_futures_unordered.rs
//! [reported by Jon Gjengset]: https://github.com/rust-lang/futures-rs/issues/2047
//!
//! ## Architecture
//!
//! The `Unordered` type stores all futures being polled in a `PinSlab` (Inspired by
//! the [slab] crate).
//! A slab is capable of utomatically reclaiming storage at low cost, and will
//! maintain decent memory locality.
//! A `PinSlab` is different from a `Slab` in how it allocates the memory regions it
//! uses to store objects.
//! While a regular `Slab` is simply backed by a vector which grows as appropriate,
//! this approach is not viable for pinning, since it would cause the objects to
//! move while being reallocated.
//! Instead `PinSlab` maintains a growable collection of fixed-size memory regions,
//! allowing it to store and reference immovable objects through the [pin API].
//! Each future inserted into the slab is assigned an _index_, which we will be
//! using below.
//! We now call the inserted future a _task_, and you can think of this index as a
//! unique task identifier.
//!
//! [slab]: https://github.com/carllerche/slab
//! [pin API]: https://doc.rust-lang.org/std/pin/index.html
//!
//! Next to the slab we maintain two bitsets, one _active_ and one _alternate_.
//! When a task registers interest in waking up, the bit associated with its index
//! is set in the active set, and the latest waker passed into `Unordered` is called
//! to wake it up.
//! Once `Unordered` is polled, it atomically swaps the active and alternate
//! bitsets, waits until it has exclusive access to the now _alternate_ bitset, and
//! drains it from all the indexes which have been flagged to determine which tasks
//! to poll.
//! Each task is then polled _once_ in order.
//! If the task is [`Ready`], its result is added to a result queue.
//!
//! Unicycle now prioritizes draining the result queue above everything else. Once
//! it is empty, we start the cycle over again.

#[doc(hidden)]
pub use self::bit_set::{AtomicBitSet, BitSet};
#[doc(hidden)]
pub use self::pin_slab::PinSlab;
use self::wake_set::{SharedWakeSet, WakeSet};
use self::waker::SharedWaker;
use futures_core::Stream;
use std::{
    collections::VecDeque,
    future::Future,
    iter, mem,
    pin::Pin,
    ptr,
    sync::Arc,
    task::{Context, Poll},
};

mod bit_set;
mod lock;
mod pin_slab;
mod wake_set;
mod waker;

/// Data that is shared across all sub-tasks.
struct Shared {
    /// The currently registered parent waker.
    waker: SharedWaker,
    /// The currently registered wake set.
    wake_set: SharedWakeSet,
}

impl Shared {
    /// Construct new shared data.
    fn new() -> Self {
        Self {
            waker: SharedWaker::new(),
            wake_set: SharedWakeSet::new(),
        }
    }
}

/// A container for an unordered collection of [Future]s.
pub struct Unordered<F>
where
    F: Future,
{
    /// Indexes that needs to be polled after they have been added.
    pollable: Vec<usize>,
    /// Slab of futures being polled.
    /// They need to be pinned on the heap, since the slab might grow to
    /// accomodate more futures.
    slab: PinSlab<F>,
    /// The largest index inserted into the slab so far.
    max_capacity: usize,
    /// Shared parent waker.
    /// Includes the current wake target. Each time we poll, we swap back and
    /// forth between this and `wake_alternate`.
    shared: Arc<Shared>,
    /// Alternate wake set, used for growing the existing set when futures are
    /// added. This is then swapped out with the active set to receive polls.
    wake_alternate: *mut WakeSet,
    /// Flag intent to lock wake_alternative exclusively.
    /// We set this flag instead of blocking on locking `wake_alternate` if
    /// locking fails.
    lock_wake_alternate: bool,
    /// Pending outgoing results. Uses a queue to avoid interrupting polling.
    results: VecDeque<F::Output>,
}

unsafe impl<F> Send for Unordered<F> where F: Future {}
unsafe impl<F> Sync for Unordered<F> where F: Future {}

impl<F> Unpin for Unordered<F> where F: Future {}

impl<F> Unordered<F>
where
    F: Future,
{
    /// Construct a new, empty [Unordered].
    pub fn new() -> Self {
        let alternate = WakeSet::locked();

        Self {
            pollable: Vec::with_capacity(16),
            slab: PinSlab::new(),
            max_capacity: 0,
            shared: Arc::new(Shared::new()),
            wake_alternate: Box::into_raw(Box::new(alternate)),
            lock_wake_alternate: false,
            results: VecDeque::new(),
        }
    }

    /// Test if the collection of futures is empty.
    pub fn is_empty(&self) -> bool {
        self.slab.is_empty()
    }

    /// Add the given future to the [Unordered] stream.
    ///
    /// Newly added futures are guaranteed to be polled, but there is no
    /// guarantee in which order this will happen.
    pub fn push(&mut self, future: F) {
        let index = self.slab.insert(future);
        self.max_capacity = usize::max(self.max_capacity, index + 1);
        self.pollable.push(index);
    }
}

impl<F> Default for Unordered<F>
where
    F: Future,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<F> Drop for Unordered<F>
where
    F: Future,
{
    fn drop(&mut self) {
        // We intend to drop both wake sets. Therefore we need exclusive access
        // to both wakers. Unfortunately that means that at this point, any call
        // to wakes will have to serialize behind the shared wake set while the
        // alternate set is being dropped.
        let _write = self.shared.wake_set.prevent_drop_write();

        // Safety: we uniquely own `wake_alternate`, so we are responsible for
        // dropping it. This is asserted when we swap it out during a poll by
        // calling WakeSet::lock_exclusive. We are also the _only_ one
        // swapping `wake_alternative`, so we know that can't happen here.
        unsafe {
            drop(Box::from_raw(self.wake_alternate));
        }
    }
}

impl<F> Stream for Unordered<F>
where
    F: Future,
{
    type Item = F::Output;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let Self {
            ref mut pollable,
            ref mut results,
            ref mut slab,
            ref shared,
            ref mut wake_alternate,
            ref mut lock_wake_alternate,
            max_capacity,
            ..
        } = *self.as_mut();

        // Return pending result.
        if let Some(value) = results.pop_front() {
            cx.waker().wake_by_ref();
            return Poll::Ready(Some(value));
        }

        if slab.is_empty() {
            // Nothing to poll, nothing to add. End the stream since we don't have work to do.
            return Poll::Ready(None);
        }

        // Note: We defer swapping the waker until we are here since we `wake_by_ref` when
        // reading results, and if we don't have any child tasks (slab is empty) no one would
        // benefit from an update anyways.
        if !shared.waker.swap(cx.waker()) {
            return Poll::Pending;
        }

        let wake_last = unsafe {
            if !*lock_wake_alternate {
                {
                    let wake_set = (**wake_alternate).as_local_mut();

                    if wake_set.set.capacity() <= max_capacity {
                        wake_set.set.reserve(max_capacity);
                    }
                }

                // Unlock. At this position, if someone adds an element to the wake set they are
                // also bound to call wake, which will cause us to wake up.
                //
                // There is a race going on between locking and unlocking, and it's beneficial
                // for child tasks to observe the locked state of the wake set so they refetch
                // the other set instead of having to wait until another wakeup.
                (**wake_alternate).unlock_exclusive();

                let next = mem::replace(wake_alternate, ptr::null_mut());
                *wake_alternate = shared.wake_set.swap(next);

                *lock_wake_alternate = true;
            }

            // Make sure no one else is using the alternate wake.
            //
            // Safety: We are the only one swapping wake_alternate, so at
            // this point we know that we have access to the most recent
            // active set. We _must_ call lock_exclusive before we
            // can punt this into a mutable reference though, because at
            // this point inner futures will still have access to references
            // to it (under a lock!). We must wait for these to expire.
            if !(**wake_alternate).try_lock_exclusive() {
                cx.waker().wake_by_ref();
                return Poll::Pending;
            }

            *lock_wake_alternate = false;
            // Safety: While this is live we must _not_ mess with
            // `wake_alternate` in any way.
            (**wake_alternate).as_local_mut()
        };

        let indexes = iter::from_fn(|| pollable.pop()).chain(wake_last.set.drain());

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
            // reference, with referential access to `shared`.
            let result = self::waker::poll_with_ref(shared, index, move |cx| fut.poll(cx));

            if let Poll::Ready(result) = result {
                results.push_back(result);
                let removed = slab.remove(index);
                debug_assert!(removed);
            }
        }

        // Return produced result.
        if let Some(value) = results.pop_front() {
            cx.waker().wake_by_ref();
            return Poll::Ready(Some(value));
        }

        Poll::Pending
    }
}
