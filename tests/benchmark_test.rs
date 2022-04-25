#![cfg(features = "futures-rs")]

use futures::channel::oneshot;
use futures::future;
use futures::stream::StreamExt;
use futures::task::Poll;
use std::collections::VecDeque;
use std::thread;

const NUM: usize = 10_000;
const EXPECTED: usize = 50005000;

/// Note: I use this test to detect deadlocks in unicycle. It aggressively
/// polls the `Unordered` collection, and wakeups are generated on a different
/// thread.
#[ignore]
#[tokio::test]
async fn benchmark_oneshots_unicycle() {
    for i in 0..1000 {
        use unicycle::FuturesUnordered;

        let mut txs = VecDeque::with_capacity(NUM);
        let mut rxs = FuturesUnordered::new();

        for _ in 0..NUM {
            let (tx, rx) = oneshot::channel();
            txs.push_back(tx);
            rxs.push(rx);
        }

        thread::spawn(move || {
            let mut num = 1usize;

            while let Some(tx) = txs.pop_front() {
                let _ = tx.send(num);
                num += 1;
            }
        });

        future::poll_fn(move |cx| {
            let mut result = 0usize;

            loop {
                if let Poll::Ready(ready) = rxs.poll_next_unpin(cx) {
                    match ready {
                        Some(num) => result = result.wrapping_add(num.unwrap()),
                        None => break,
                    }
                }
            }

            assert_eq!(EXPECTED, result);
            Poll::Ready(())
        })
        .await;

        println!("tick: {}", i);
    }
}
