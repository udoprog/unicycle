//! [<img alt="github" src="https://img.shields.io/badge/github-udoprog/unicycle-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/unicycle)
//! [<img alt="crates.io" src="https://img.shields.io/crates/v/unicycle.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/unicycle)
//! [<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-unicycle-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/unicycle)
//!
//! A scheduler for driving a large number of futures.
//!
//! Unicycle provides a collection of [Unordered] types:
//!
//! * [FuturesUnordered]
//! * [StreamsUnordered]
//! * [IndexedStreamsUnordered]
//!
//! These are async abstractions that runs a set of futures or streams which may
//! complete in any order.
//! Similarly to [FuturesUnordered][futures-rs] from the [futures crate].
//! But we aim to provide a stronger guarantee of fairness (see below), and
//! better memory locality for the futures being pollled.
//!
//! **Note:** This project is experimental. It involves some amount of unsafe and
//! possibly bad assumptions which needs to be either vetted or removed before you
//! should consider putting it in production.
//!
//! <br>
//!
//! ## Features
//!
//! * `parking-lot` - To enable locking using the [parking_lot] crate (default).
//! * `futures-rs` - Enable the used of the Stream type from [futures-rs].
//!   This is required to get access to [StreamsUnordered] and
//!   [IndexedStreamsUnordered] since these wrap over [futures-rs] types. (default)
//!
//! <br>
//!
//! ## Examples
//!
//! ```
//! use std::time::Duration;
//!
//! use tokio::time;
//! use unicycle::FuturesUnordered;
//!
//! # #[cfg(miri)] fn main() {}
//! # #[cfg(not(miri))]
//! # #[tokio::main(flavor = "current_thread", start_paused = true)]
//! # async fn main() {
//! let mut futures = FuturesUnordered::new();
//!
//! futures.push(time::sleep(Duration::from_secs(2)));
//! futures.push(time::sleep(Duration::from_secs(3)));
//! futures.push(time::sleep(Duration::from_secs(1)));
//!
//! while let Some(_) = futures.next().await {
//!     println!("tick");
//! }
//!
//! println!("done!");
//! # }
//! ```
//!
//! [Unordered] types can be created from iterators:
//!
//! ```
//! use std::time::Duration;
//!
//! use tokio::time;
//! use unicycle::FuturesUnordered;
//!
//! # #[cfg(miri)] fn main() {}
//! # #[cfg(not(miri))]
//! # #[tokio::main(flavor = "current_thread", start_paused = true)]
//! # async fn main() {
//! let mut futures = Vec::new();
//!
//! futures.push(time::sleep(Duration::from_secs(2)));
//! futures.push(time::sleep(Duration::from_secs(3)));
//! futures.push(time::sleep(Duration::from_secs(1)));
//!
//! let mut futures = futures.into_iter().collect::<FuturesUnordered<_>>();
//!
//! while let Some(_) = futures.next().await {
//!     println!("tick");
//! }
//!
//! println!("done!");
//! # }
//! ```
//!
//! <br>
//!
//! ## Fairness
//!
//! You can think of abstractions like Unicycle as schedulers. They are provided
//! a set of child tasks, and try to do their best to drive them to completion.
//! In this regard, it's interesting to talk about _fairness_ in how the tasks
//! are being driven.
//!
//! The current implementation of [FuturesUnordered][futures-rs] maintains a
//! queue of tasks interested in waking up. As a task is woken up it's added to
//! the head of this queue to signal its interest in being polled. When
//! [FuturesUnordered][futures-rs] works it drains this queue in a loop and
//! polls the associated task. This process has a side effect where tasks who
//! aggressively signal interest in waking up will receive priority and be
//! polled more frequently. Since there is a higher chance that while the queue
//! is being drained, their interest will be re-added at the head of the queue
//! immeidately. This can lead to instances where a small number of tasks can
//! can cause the polling loop of [FuturesUnordered][futures-rs] to [spin
//! abnormally]. This issue was [reported by Jon Gjengset] and is improved on by
//! [limiting the amount FuturesUnordered is allowed to spin].
//!
//! Unicycle addresses this by limiting how frequently a child task may be
//! polled per _polling cycle_. This is done by tracking polling interest in two
//! separate sets. Once we are polled, we swap out the active set then take the
//! swapped out set and use as a basis for what to poll in order while limiting
//! ourselves to only poll _once_ per child task. Additional wakeups are only
//! registered in the swapped in set which will be polled the next cycle.
//!
//! This way we hope to achieve a higher degree of fairness, never favoring the
//! behavior of one particular task.
//!
//! <br>
//!
//! ## Architecture
//!
//! The [Unordered] type stores all futures being polled in a continuous storage
//! [slab] where each future is stored in a separate allocation. The header of
//! this storage is atomically reference counted and can be used to construct a
//! waker without additional allocation.
//!
//! Next to the slab we maintain two [BitSets][BitSet], one _active_ and one
//! _alternate_. When a task registers interest in waking up, the bit associated
//! with its index is set in the active set, and the latest waker passed into
//! [Unordered] is called to wake it up. Once [Unordered] is polled, it
//! atomically swaps the active and alternate [BitSets][BitSet], waits until it
//! has exclusive access to the now _alternate_ [BitSet], and drains it from all
//! the indexes which have been flagged to determine which tasks to poll. Each
//! task is then polled _once_ in order. If the task is [Ready], its result is
//! yielded. After we receive control again, we continue draining the alternate
//! set in this manner, until it is empty. When this is done we yield once, then
//! we start the cycle over again.
//!
//! [BitSet]: https://docs.rs/uniset/latest/uniset/struct.BitSet.html
//! [futures crate]: https://docs.rs/futures/latest/futures
//! [futures-rs]: https://crates.io/crates/futures
//! [futures-rs]: https://docs.rs/futures/latest/futures/stream/struct.FuturesUnordered.html
//! [FuturesUnordered]: https://docs.rs/unicycle/latest/unicycle/type.FuturesUnordered.html
//! [IndexedStreamsUnordered]: https://docs.rs/unicycle/latest/unicycle/type.IndexedStreamsUnordered.html
//! [limiting the amount FuturesUnordered is allowed to spin]: https://github.com/rust-lang/futures-rs/pull/2049
//! [parking_lot]: https://crates.io/crates/parking_lot
//! [pin API]: https://doc.rust-lang.org/std/pin/index.html
//! [Ready]: https://doc.rust-lang.org/std/task/enum.Poll.html
//! [reported by Jon Gjengset]: https://github.com/rust-lang/futures-rs/issues/2047
//! [Slab]: https://docs.rs/slab/latest/slab/struct.Slab.html
//! [slab]: https://github.com/carllerche/slab
//! [spin abnormally]: https://github.com/udoprog/unicycle/blob/main/tests/spinning_futures_unordered_test.rs
//! [StreamsUnordered]: https://docs.rs/unicycle/latest/unicycle/type.StreamsUnordered.html
//! [Unordered]: https://docs.rs/unicycle/latest/unicycle/struct.Unordered.html

#![deny(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(rustdoc::broken_intra_doc_links)]
#![allow(clippy::should_implement_trait)]

mod lock;
mod shared;
mod task;
#[cfg(test)]
mod tests;
mod wake_set;
mod waker;

use std::future::Future;
use std::iter;
use std::marker;
use std::pin::Pin;
use std::task::{Context, Poll};

use self::task::Storage;
use self::wake_set::WakeSet;
#[cfg(feature = "futures-rs")]
use futures_core::{FusedFuture, FusedStream, Stream};

/// Our very own homemade `ready!` impl.
macro_rules! ready {
    ($expr:expr) => {
        match $expr {
            Poll::Ready(value) => value,
            Poll::Pending => return Poll::Pending,
        }
    };
}

/// A container for an unordered collection of [Future]s.
///
/// # Examples
///
/// ```
/// use std::time::Duration;
///
/// use tokio::time;
///
/// # #[cfg(miri)] fn main() {}
/// # #[cfg(not(miri))]
/// # #[tokio::main(flavor = "current_thread", start_paused = true)]
/// # async fn main() {
/// let mut futures = unicycle::FuturesUnordered::new();
///
/// futures.push(time::sleep(Duration::from_secs(2)));
/// futures.push(time::sleep(Duration::from_secs(3)));
/// futures.push(time::sleep(Duration::from_secs(1)));
///
/// while let Some(_) = futures.next().await {
///     println!("tick");
/// }
///
/// println!("done!");
/// }
/// ```
pub type FuturesUnordered<T> = Unordered<T, Futures>;

mod private {
    pub trait Sealed {}

    impl Sealed for super::Futures {}
    #[cfg(feature = "futures-rs")]
    impl Sealed for super::Streams {}
    #[cfg(feature = "futures-rs")]
    impl Sealed for super::IndexedStreams {}
}

/// Trait implemented by sentinels for the [Unordered] type.
pub trait Sentinel: self::private::Sealed {}

/// Sentinel type for futures.
///
/// [Unordered] instances which handle futures have the signature
/// `Unordered<T, Futures>`, since it allows for a different implementation of
/// [Stream].
pub struct Futures(());

impl Sentinel for Futures {}

/// A container for an unordered collection of [Future]s or [Stream]s.
///
/// You should use one of the following type aliases to construct it:
/// * [FuturesUnordered]
/// * [StreamsUnordered]
/// * [IndexedStreamsUnordered]
///
/// # Examples
///
/// ```
/// use std::time::Duration;
///
/// use tokio::time;
///
/// # #[cfg(miri)] fn main() {}
/// # #[cfg(not(miri))]
/// # #[tokio::main(flavor = "current_thread", start_paused = true)]
/// # async fn main() {
/// let mut futures = unicycle::FuturesUnordered::new();
///
/// futures.push(time::sleep(Duration::from_secs(2)));
/// futures.push(time::sleep(Duration::from_secs(3)));
/// futures.push(time::sleep(Duration::from_secs(1)));
///
/// while let Some(_) = futures.next().await {
///     println!("tick");
/// }
///
/// println!("done!");
/// }
/// ```
pub struct Unordered<T, S>
where
    S: Sentinel,
{
    /// Slab of futures being polled.
    /// They need to be pinned on the heap, since the slab might grow to
    /// accomodate more futures.
    slab: Storage<T>,
    /// Alternate wake set, used for growing the existing set when futures are
    /// added. This is then swapped out with the active set to receive polls.
    alternate: *mut WakeSet,
    /// Marker for the sentinel.
    _marker: marker::PhantomData<S>,
}

// Safety: Unordered is ultimately a container of `T`, and is `Send` only if `T`
// themselves are `Send`.
unsafe impl<T, S> Send for Unordered<T, S>
where
    T: Send,
    S: Sentinel,
{
}

// Safety: Unordered is ultimately a container of `T`, and is `Sync` only if `T`
// themselves are `Sync`.
unsafe impl<T, S> Sync for Unordered<T, S>
where
    T: Sync,
    S: Sentinel,
{
}

impl<T, S> Unpin for Unordered<T, S> where S: Sentinel {}

impl<T, S> Unordered<T, S>
where
    S: Sentinel,
    Self: PollNext,
{
    /// Creates a future that resolves to the next item in the unordered set.
    ///
    /// Functions like [`StreamExt::next`] would from the [futures] crate, but
    /// doesn't depend on the [Stream] trait.
    ///
    /// [`StreamExt::next`]: https://docs.rs/futures/latest/futures/stream/trait.StreamExt.html#method.next
    /// [futures]: https://crates.io/crates/futures
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    ///
    /// use tokio::time;
    /// use unicycle::FuturesUnordered;
    ///
    /// # #[cfg(miri)] fn main() {}
    /// # #[cfg(not(miri))]
    /// # #[tokio::main(flavor = "current_thread", start_paused = true)]
    /// # async fn main() {
    /// let mut futures = FuturesUnordered::new();
    ///
    /// futures.push(time::sleep(Duration::from_secs(2)));
    /// futures.push(time::sleep(Duration::from_secs(3)));
    /// futures.push(time::sleep(Duration::from_secs(1)));
    ///
    /// while let Some(_) = futures.next().await {
    ///     println!("tick");
    /// }
    ///
    /// println!("done!");
    /// # }
    /// ```
    pub fn next(&mut self) -> Next<'_, Self> {
        Next(self)
    }
}

/// Future returned by [Unordered::next].
pub struct Next<'a, T>(&'a mut T);

impl<T> Future for Next<'_, T>
where
    T: Unpin + PollNext,
{
    type Output = Option<T::Item>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        Pin::new(&mut *self.0).poll_next(cx)
    }
}

impl<T> FuturesUnordered<T> {
    /// Construct a new, empty [FuturesUnordered].
    ///
    /// # Examples
    ///
    /// ```
    /// use unicycle::FuturesUnordered;
    ///
    /// let mut futures = FuturesUnordered::new();
    /// assert!(futures.is_empty());
    ///
    /// futures.push(async { 42 });
    /// ```
    pub fn new() -> Self {
        Self::new_internal()
    }
}

/// Trait for providing a `poll_next` implementation for various unordered set
/// types.
///
/// This is like the lightweight unicycle version of the [Stream] trait, but we
/// provide it here so we can shim in our own generic [next] implementation.
///
/// [next]: Unordered::next
pub trait PollNext {
    /// The output of the poll.
    type Item;

    /// Poll the stream for the next item.
    ///
    /// Once this completes with `Poll::Ready(None)`, no more items are expected
    /// and it should not be polled again.
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
}

impl<T> PollNext for FuturesUnordered<T>
where
    T: Future,
{
    type Item = T::Output;

    /// Internal poll function for `FuturesUnordered<T>`.
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<T::Output>> {
        let Self {
            ref mut slab,
            ref mut alternate,
            ..
        } = *self.as_mut();

        if slab.is_empty() {
            // Nothing to poll, nothing to add. End the stream since we don't have work to do.
            return Poll::Ready(None);
        }

        // Safety: We have exclusive access to Unordered, which is the only
        // implementation that is trying to swap the wake sets.
        let (non_empty, wake_last) =
            ready!(unsafe { slab.shared().poll_swap_active(cx, alternate) });

        for index in wake_last.drain() {
            // NB: Since we defer pollables a little, a future might
            // have been polled and subsequently removed from the slab.
            // So we don't treat this as an error here.
            // If on the other hand it was removed _and_ re-added, we have
            // a case of a spurious poll. Luckily, that doesn't bother a
            // future much.
            let (header, fut) = match slab.get_pin_mut(index) {
                Some(value) => value,
                None => continue,
            };

            // Construct a new lightweight waker only capable of waking by
            // reference, with referential access to `shared`.
            let result = self::waker::poll_with_ref(header, move |cx| fut.poll(cx));

            if let Poll::Ready(result) = result {
                let removed = slab.remove(index);
                debug_assert!(removed);
                return Poll::Ready(Some(result));
            }
        }

        if slab.is_empty() {
            return Poll::Ready(None);
        }

        // We need to wake again to take care of the alternate set that was
        // swapped in.
        if non_empty {
            cx.waker().wake_by_ref();
        }

        Poll::Pending
    }
}

impl<T, S> Unordered<T, S>
where
    S: Sentinel,
{
    #[inline(always)]
    fn new_internal() -> Self {
        Self {
            slab: Storage::new(),
            alternate: Box::into_raw(Box::new(WakeSet::locked())),
            _marker: marker::PhantomData,
        }
    }

    /// Get the number of elements in the collection of futures.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::future::Ready;
    ///
    /// use unicycle::FuturesUnordered;
    ///
    /// let mut futures = FuturesUnordered::<Ready<()>>::new();
    /// assert_eq!(futures.len(), 0);
    /// assert!(futures.is_empty());
    /// ```
    pub fn len(&self) -> usize {
        self.slab.len()
    }

    /// Test if the collection of futures is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::future::Ready;
    ///
    /// use unicycle::FuturesUnordered;
    ///
    /// let mut futures = FuturesUnordered::<Ready<()>>::new();
    /// assert!(futures.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.slab.is_empty()
    }

    /// Push the given future or stream to [Unordered] and return its task
    /// index.
    ///
    /// Newly added futures are guaranteed to be polled, but there is no
    /// guarantee in which order this will happen.
    ///
    /// Pushed tasks are pinned by the [Unordered] collection automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// use unicycle::FuturesUnordered;
    ///
    /// let mut futures = FuturesUnordered::new();
    /// assert!(futures.is_empty());
    /// futures.push(async { 42 });
    /// assert!(!futures.is_empty());
    /// ```
    pub fn push(&mut self, future: T) -> usize {
        let index = self.slab.insert(future);

        let (old, new) = {
            // Safety: At this point we know we have exclusive access to the set.
            let set = unsafe { (*self.alternate).as_mut_set() };
            let old = set.capacity();
            set.set(index);
            let new = set.capacity();
            (old, new)
        };

        // Fast Path: Did not grow the alternate set, so no need to grow the
        // active set either.
        if new <= old {
            return index;
        }

        // Slow Path: Swap out the active set and grow it to accomodate the same
        // number of elements as the now alternate set was grown to.
        // This works out, because if it's non-empty, the next time we poll
        // the unordered set it will be processed. It it's empty, it will be
        // swapped out with the active set which now contains the newly added
        // futures.
        // Safety: We have unique access to the alternate set being modified.
        unsafe {
            self.slab
                .shared()
                .swap_active(&mut self.alternate)
                .reserve(new);
        }

        index
    }

    /// Get a pinned mutable reference to the stream or future at the given
    /// index.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::future::Future;
    ///
    /// use unicycle::FuturesUnordered;
    /// use futures::future::poll_fn;
    ///
    /// # #[cfg(miri)] fn main() {}
    /// # #[cfg(not(miri))]
    /// # #[tokio::main(flavor = "current_thread", start_paused = true)]
    /// # async fn main() {
    ///     let mut futures = FuturesUnordered::new();
    ///     let index = futures.push(async { 42 });
    ///
    ///     let result = poll_fn(|cx| {
    ///         futures.get_pin_mut(index).expect("expected future").poll(cx)
    ///     }).await;
    ///
    ///     assert_eq!(result, 42);
    /// # }
    /// ```
    pub fn get_pin_mut(&mut self, index: usize) -> Option<Pin<&mut T>> {
        Some(self.slab.get_pin_mut(index)?.1)
    }

    /// Get a mutable reference to the stream or future at the given index.
    /// Requires that the stores stream or future is [Unpin].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::pin::Pin;
    /// use std::future::Future;
    ///
    /// use unicycle::FuturesUnordered;
    /// use futures::future::{ready, poll_fn};
    ///
    /// # #[cfg(miri)] fn main() {}
    /// # #[cfg(not(miri))]
    /// # #[tokio::main(flavor = "current_thread", start_paused = true)]
    /// # async fn main() {
    ///     let mut futures = FuturesUnordered::new();
    ///     let index = futures.push(ready(42));
    ///
    ///     let result = poll_fn(|cx| {
    ///         Pin::new(futures.get_mut(index).expect("expected future")).poll(cx)
    ///     }).await;
    ///
    ///     assert_eq!(result, 42);
    /// # }
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T>
    where
        T: Unpin,
    {
        self.slab.get_mut(index)
    }
}

impl<T> Default for Unordered<T, Futures> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, S> Drop for Unordered<T, S>
where
    S: Sentinel,
{
    fn drop(&mut self) {
        // Cancel all child futures in an attempt to prevent them from
        // attempting to call wake on the shared wake set.
        self.slab.clear();

        // We intend to drop both wake sets. Therefore we need exclusive access
        // to both wakers. Unfortunately that means that at this point, any call
        // to wakes will have to serialize behind the shared wake set while the
        // alternate set is being dropped.
        let _write = self.slab.shared().wake_set.prevent_drop_write();

        // Safety: we uniquely own `alternate`, so we are responsible for
        // dropping it. This is asserted when we swap it out during a poll by
        // calling WakeSet::lock_exclusive. We are also the _only_ one
        // swapping `wake_alternative`, so we know that can't happen here.
        unsafe {
            drop(Box::from_raw(self.alternate));
        }
    }
}

impl<T, S> iter::Extend<T> for Unordered<T, S>
where
    S: Sentinel,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for value in iter {
            self.push(value);
        }
    }
}

impl<T> iter::FromIterator<T> for FuturesUnordered<T>
where
    T: Future,
{
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut futures = FuturesUnordered::new();
        futures.extend(iter);
        futures
    }
}

macro_rules! cfg_futures_rs {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "futures-rs")]
            #[cfg_attr(docsrs, doc(cfg(feature = "futures-rs")))]
            $item
        )*
    }
}

cfg_futures_rs! {
    /// Sentinel type for streams.
    ///
    /// [Unordered] instances which handle futures have the signature
    /// `Unordered<T, Streams>`, since it allows for a different implementation of
    /// [Stream].
    pub struct Streams(());

    impl Sentinel for Streams {}

    /// Sentinel type for streams which are indexed - for each value they yield,
    /// they also yield the task identifier associated with them.
    ///
    /// [Unordered] instances which handle futures have the signature
    /// `Unordered<T, IndexedStreams>`, since it allows for a different
    /// implementation of [Stream].
    pub struct IndexedStreams(());

    impl Sentinel for IndexedStreams {}

    /// A container for an unordered collection of [Stream]s.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::error::Error;
    ///
    /// use tokio::net::TcpListener;
    /// use tokio::time;
    /// use tokio_util::codec::{Framed, LengthDelimitedCodec};
    ///
    /// # #[tokio::main(flavor = "current_thread", start_paused = true)]
    /// # async fn main() -> Result<(), Box<dyn Error>> {
    /// let mut listener = TcpListener::bind("127.0.0.1:8080").await?;
    /// let mut clients = unicycle::StreamsUnordered::new();
    ///
    /// loop {
    ///     tokio::select! {
    ///         result = listener.accept() => {
    ///             let (stream, _) = result?;
    ///             clients.push(Framed::new(stream, LengthDelimitedCodec::new()));
    ///         },
    ///         Some(frame) = clients.next() => {
    ///             println!("received frame: {:?}", frame);
    ///         }
    ///     }
    /// }
    /// # }
    /// ```
    pub type StreamsUnordered<T> = Unordered<T, Streams>;

    /// A container for an unordered collection of [Stream]s, which also yields the
    /// index that produced the next item.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::error::Error;
    ///
    /// use tokio::net::TcpListener;
    /// use tokio::time;
    /// use tokio_util::codec::{Framed, LengthDelimitedCodec};
    ///
    /// # #[tokio::main(flavor = "current_thread", start_paused = true)]
    /// # async fn main() -> Result<(), Box<dyn Error>> {
    /// let mut listener = TcpListener::bind("127.0.0.1:8080").await?;
    /// let mut clients = unicycle::IndexedStreamsUnordered::new();
    ///
    /// loop {
    ///     tokio::select! {
    ///         result = listener.accept() => {
    ///             let (stream, _) = result?;
    ///             clients.push(Framed::new(stream, LengthDelimitedCodec::new()));
    ///         },
    ///         Some((index, frame)) = clients.next() => {
    ///             match frame {
    ///                 Some(frame) => println!("{}: received frame: {:?}", index, frame),
    ///                 None => println!("{}: client disconnected", index),
    ///             }
    ///         }
    ///     }
    /// }
    /// # }
    /// ```
    pub type IndexedStreamsUnordered<T> = Unordered<T, IndexedStreams>;

    impl<T> StreamsUnordered<T> {
        /// Construct a new, empty [StreamsUnordered].
        ///
        /// # Examples
        ///
        /// ```
        /// use tokio_stream::iter;
        /// use unicycle::StreamsUnordered;
        ///
        /// # #[cfg(miri)] fn main() {}
        /// # #[cfg(not(miri))]
        /// # #[tokio::main(flavor = "current_thread", start_paused = true)]
        /// # async fn main() {
        /// let mut streams = StreamsUnordered::new();
        /// assert!(streams.is_empty());
        ///
        /// streams.push(iter(vec![1, 2, 3, 4]));
        /// streams.push(iter(vec![5, 6, 7, 8]));
        ///
        /// let mut received = Vec::new();
        ///
        /// while let Some(value) = streams.next().await {
        ///     received.push(value);
        /// }
        ///
        /// assert_eq!(vec![5, 1, 6, 2, 7, 3, 8, 4], received);
        /// # }
        /// ```
        pub fn new() -> Self {
            Self::new_internal()
        }
    }

    impl<T> IndexedStreamsUnordered<T> {
        /// Construct a new, empty [IndexedStreamsUnordered].
        ///
        /// This is the same as [StreamsUnordered], except that it yields the index
        /// of the stream who'se value was just yielded, alongside the yielded
        /// value.
        ///
        /// # Examples
        ///
        /// ```
        /// use tokio_stream::iter;
        /// use unicycle::IndexedStreamsUnordered;
        ///
        /// # #[cfg(miri)] fn main() {}
        /// # #[cfg(not(miri))]
        /// # #[tokio::main(flavor = "current_thread", start_paused = true)]
        /// # async fn main() {
        /// let mut streams = IndexedStreamsUnordered::new();
        /// assert!(streams.is_empty());
        ///
        /// streams.push(iter(vec![1, 2]));
        /// streams.push(iter(vec![5, 6]));
        ///
        /// let mut received = Vec::new();
        ///
        /// while let Some(value) = streams.next().await {
        ///     received.push(value);
        /// }
        ///
        /// assert_eq!(
        ///     vec![
        ///         (1, Some(5)),
        ///         (0, Some(1)),
        ///         (1, Some(6)),
        ///         (0, Some(2)),
        ///         (1, None),
        ///         (0, None)
        ///     ],
        ///     received
        /// );
        /// # }
        /// ```
        pub fn new() -> Self {
            Self::new_internal()
        }
    }

    /// Provide `Stream` implementation through `PollNext`.
    impl<T, S> Stream for Unordered<T, S>
    where
        S: Sentinel,
        Self: PollNext,
    {
        type Item = <Self as PollNext>::Item;

        fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            <Self as PollNext>::poll_next(self, cx)
        }
    }

    impl<T, S> FusedStream for Unordered<T, S> where S: Sentinel, Self: PollNext, {
        fn is_terminated(&self) -> bool {
            self.is_empty()
        }
    }

    impl<T> PollNext for StreamsUnordered<T>
    where
        T: Stream,
    {
        type Item = T::Item;

        fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            let Self {
                ref mut slab,
                ref mut alternate,
                ..
            } = *self.as_mut();

            if slab.is_empty() {
                // Nothing to poll, nothing to add. End the stream since we don't have work to do.
                return Poll::Ready(None);
            }

            // Safety: We have exclusive access to Unordered, which is the only
            // implementation that is trying to swap the wake sets.
            let (non_empty, wake_last) = ready!(unsafe { slab.shared().poll_swap_active(cx, alternate) });

            for index in wake_last.drain() {
                // NB: Since we defer pollables a little, a future might
                // have been polled and subsequently removed from the slab.
                // So we don't treat this as an error here.
                // If on the other hand it was removed _and_ re-added, we have
                // a case of a spurious poll. Luckily, that doesn't bother a
                // future much.
                let (header, stream) = match slab.get_pin_mut(index) {
                    Some(value) => value,
                    None => continue,
                };

                // Construct a new lightweight waker only capable of waking by
                // reference, with referential access to `shared`.
                let result = self::waker::poll_with_ref(header, move |cx| stream.poll_next(cx));

                if let Poll::Ready(result) = result {
                    match result {
                        Some(value) => {
                            cx.waker().wake_by_ref();
                            slab.shared().wake_set.wake(index);
                            return Poll::Ready(Some(value));
                        }
                        None => {
                            let removed = slab.remove(index);
                            debug_assert!(removed);
                        }
                    }
                }
            }

            // We have successfully polled the last snapshot.
            // Yield and make sure that we are polled again.
            if slab.is_empty() {
                return Poll::Ready(None);
            }

            // We need to wake again to take care of the alternate set that was
            // swapped in.
            if non_empty {
                cx.waker().wake_by_ref();
            }

            Poll::Pending
        }
    }

    impl<T> PollNext for IndexedStreamsUnordered<T>
    where
        T: Stream,
    {
        type Item = (usize, Option<T::Item>);

        fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            let Self {
                ref mut slab,
                ref mut alternate,
                ..
            } = *self.as_mut();

            if slab.is_empty() {
                // Nothing to poll, nothing to add. End the stream since we don't have work to do.
                return Poll::Ready(None);
            }

            // Safety: We have exclusive access to Unordered, which is the only
            // implementation that is trying to swap the wake sets.
            let (non_empty, wake_last) = ready!(unsafe { slab.shared().poll_swap_active(cx, alternate) });

            for index in wake_last.drain() {
                // NB: Since we defer pollables a little, a future might
                // have been polled and subsequently removed from the slab.
                // So we don't treat this as an error here.
                // If on the other hand it was removed _and_ re-added, we have
                // a case of a spurious poll. Luckily, that doesn't bother a
                // future much.
                let (header, stream) = match slab.get_pin_mut(index) {
                    Some((header, stream)) => (header, stream),
                    None => continue,
                };

                // Construct a new lightweight waker only capable of waking by
                // reference, with referential access to `shared`.
                let result = self::waker::poll_with_ref(header, move |cx| stream.poll_next(cx));

                if let Poll::Ready(result) = result {
                    match result {
                        Some(value) => {
                            cx.waker().wake_by_ref();
                            slab.shared().wake_set.wake(index);
                            return Poll::Ready(Some((index, Some(value))));
                        }
                        None => {
                            cx.waker().wake_by_ref();
                            let removed = slab.remove(index);
                            debug_assert!(removed);
                            return Poll::Ready(Some((index, None)));
                        }
                    }
                }
            }

            // We have successfully polled the last snapshot.
            // Yield and make sure that we are polled again.
            if slab.is_empty() {
                return Poll::Ready(None);
            }

            // We need to wake again to take care of the alternate set that was
            // swapped in.
            if non_empty {
                cx.waker().wake_by_ref();
            }

            Poll::Pending
        }
    }

    impl<T> iter::FromIterator<T> for StreamsUnordered<T>
    where
        T: Stream,
    {
        #[inline]
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            let mut streams = StreamsUnordered::new();
            streams.extend(iter);
            streams
        }
    }

    impl<T> FusedFuture for Next<'_, T>
    where
        T: Unpin + PollNext + FusedStream,
    {
        fn is_terminated(&self) -> bool {
            self.0.is_terminated()
        }
    }
}
