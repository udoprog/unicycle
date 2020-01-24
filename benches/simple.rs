#![feature(test)]

extern crate test;

use test::Bencher;

use futures::channel::oneshot;
use futures::executor::block_on;
use futures::future;
use futures::stream::{FuturesUnordered, StreamExt};
use futures::task::Poll;
use std::collections::VecDeque;
use std::thread;

const NUM: usize = 100;
const EXPECTED: usize = 5050;

#[bench]
fn oneshots_unicycle(b: &mut Bencher) {
    use unicycle::Unordered;

    b.iter(|| {
        let mut txs = VecDeque::with_capacity(NUM);
        let mut rxs = Unordered::new();

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

        block_on(future::poll_fn(move |cx| {
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
        }))
    });
}

#[bench]
fn oneshots_futures(b: &mut Bencher) {
    b.iter(|| {
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

        block_on(future::poll_fn(move |cx| {
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
        }))
    });
}

/*#[bench]
fn test_bitset(b: &mut Bencher) {
    use unicycle::Unordered;

    b.iter(|| {
        let mut rt = tokio::runtime::Runtime::new().unwrap();

        rt.block_on(async {
            let mut futures = Unordered::new();

            for _ in 0..500_000 {
                futures.push(time::delay_for(Duration::from_millis(100 + (rand::random::<f32>() * 100f32) as u64)));
            }

            let mut count = 0u32;

            while let Some(_) = futures.next().await {
                count += 1;

                if count == 500_000 {
                    break;
                }
            }

            count
        });
    });
}

#[bench]
fn test_futures(b: &mut Bencher) {
    use futures::stream::FuturesUnordered;

    b.iter(|| {
        let mut rt = tokio::runtime::Runtime::new().unwrap();

        rt.block_on(async {
            let mut futures = FuturesUnordered::new();

            for _ in 0..500_000 {
                futures.push(time::delay_for(Duration::from_millis(100 + (rand::random::<f32>() * 100f32) as u64)));
            }

            let mut count = 0u32;

            while let Some(_) = futures.next().await {
                count += 1;

                if count == 500_000 {
                    break;
                }
            }
        });
    });
}*/
