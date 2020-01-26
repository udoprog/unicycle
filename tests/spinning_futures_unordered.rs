use futures::{
    future::poll_fn,
    stream::{FuturesUnordered, Stream as _},
};
use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

struct Spinner;

impl Future for Spinner {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        println!("Hello!");
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}

#[ignore]
#[tokio::test]
async fn test_spinning_futures_unordered() {
    let futures = FuturesUnordered::new();
    futures.push(Spinner);
    pin_utils::pin_mut!(futures);

    let _ = poll_fn::<(), _>(move |cx| {
        let _ = Pin::new(&mut futures).poll_next(cx);
        panic!("We never reach this...");
    })
    .await;
}
