#![cfg(feature = "futures-rs")]

use std::pin::Pin;
use std::sync::atomic;
use std::sync::Arc;
use std::task;

use tokio_stream::iter;
use unicycle::StreamsUnordered;

#[test]
fn test_unicycle_streams() {
    let mut streams = StreamsUnordered::new();
    assert!(streams.is_empty());

    streams.push(iter(vec![1, 2, 3, 4]));
    streams.push(iter(vec![5, 6, 7, 8]));

    let mut received = Vec::new();

    futures::executor::block_on(async {
        while let Some(value) = streams.next().await {
            received.push(value);
        }
    });

    assert_eq!(vec![5, 1, 6, 2, 7, 3, 8, 4], received);
}

// See #30 for details.
#[test]
fn test_drop_with_stored_waker() {
    struct Testee {
        waker: Option<task::Waker>,
        dropped: Arc<atomic::AtomicBool>,
    }

    impl futures::Stream for Testee {
        type Item = u32;

        fn poll_next(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> task::Poll<Option<u32>> {
            println!("testee polled");
            unsafe { self.get_unchecked_mut() }.waker = Some(cx.waker().clone());
            task::Poll::Pending
        }
    }

    impl Drop for Testee {
        fn drop(&mut self) {
            println!("testee dropped");
            self.dropped.store(true, atomic::Ordering::SeqCst);
        }
    }

    let mut streams = StreamsUnordered::new();

    let dropped = Arc::new(atomic::AtomicBool::new(false));
    streams.push(Testee {
        waker: None,
        dropped: dropped.clone(),
    });

    futures::executor::block_on(async {
        let fut = streams.next();
        let res = futures::future::poll_immediate(fut).await;
        assert!(res.is_none());
    });

    drop(streams);
    assert!(dropped.load(atomic::Ordering::SeqCst));
}
