#![cfg(feature = "futures-rs")]

use futures::future::poll_fn;
use futures::stream::Stream;
use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct Spinner<'a>(&'a Cell<usize>);

impl Future for Spinner<'_> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.0.set(self.0.get() + 1);

        // Note: this will not be needed once we have a futures release with:
        // https://github.com/rust-lang/futures-rs/pull/2049
        if self.0.get() > 16 {
            return Poll::Ready(());
        }

        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

#[tokio::test]
async fn test_spinning_unordered() {
    use unicycle::FuturesUnordered;

    let count = Cell::new(0);

    let mut futures = FuturesUnordered::new();
    futures.push(Spinner(&count));
    pin_utils::pin_mut!(futures);

    let _ = poll_fn::<(), _>(move |cx| {
        // NB: needs to be polled twice to cause the bitsets to be swapped out.
        assert_eq!(Poll::Pending, Pin::new(&mut futures).poll_next(cx));
        let _ = Pin::new(&mut futures).poll_next(cx);
        Poll::Ready(())
    })
    .await;

    // Note: Unicycle guarantees each future is poll at most once.
    assert_eq!(2, count.get());
}
