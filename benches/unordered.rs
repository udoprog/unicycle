use std::sync::Arc;
use std::thread;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use crossbeam::queue::SegQueue;
use futures::channel::oneshot;
use futures::executor::block_on;
use futures::future;
use futures::stream::StreamExt as _;
use futures::task::Poll;

pub fn polling_benchmark(c: &mut Criterion) {
    {
        let mut group = c.benchmark_group("poll overhead # futures");

        for i in [10, 100, 1000, 2500, 5000, 7500, 10000].iter() {
            group.bench_with_input(BenchmarkId::new("unicycle", i), i, |b, i| {
                b.iter(|| unicycle(*i, 1))
            });
            group.bench_with_input(BenchmarkId::new("futures-rs", i), i, |b, i| {
                b.iter(|| futures_rs(*i, 1))
            });
        }
    }

    {
        let mut group = c.benchmark_group("poll overhead # threads");

        for i in [1, 10, 20, 50, 100].iter() {
            group.bench_with_input(BenchmarkId::new("unicycle", i), i, |b, i| {
                b.iter(|| unicycle(10000, *i))
            });
            group.bench_with_input(BenchmarkId::new("futures-rs", i), i, |b, i| {
                b.iter(|| futures_rs(10000, *i))
            });
        }
    }

    fn unicycle(num: usize, threads: usize) -> usize {
        use std::pin::Pin;
        use unicycle::{FuturesUnordered, PollNext};

        let txs = SegQueue::new();
        let mut rxs = FuturesUnordered::new();

        let mut expected = 0usize;

        for i in 0..num {
            expected = expected.wrapping_add(i);
            let (tx, rx) = oneshot::channel();
            txs.push((i, tx));
            rxs.push(rx);
        }

        let txs = Arc::new(txs);

        for _ in 0..threads {
            let txs = txs.clone();

            thread::spawn(move || {
                while let Some((n, tx)) = txs.pop() {
                    let _ = tx.send(n);
                }
            });
        }

        let result = block_on(future::poll_fn(move |cx| {
            let mut result = 0usize;

            loop {
                if let Poll::Ready(ready) = Pin::new(&mut rxs).poll_next(cx) {
                    match ready {
                        Some(num) => result = result.wrapping_add(num.unwrap()),
                        None => break,
                    }
                }
            }

            Poll::Ready(expected)
        }));

        assert_eq!(expected, result);
        result
    }

    fn futures_rs(num: usize, threads: usize) -> usize {
        use futures::stream::FuturesUnordered;

        let txs = SegQueue::new();
        let mut rxs = FuturesUnordered::new();

        let mut expected = 0usize;

        for i in 0..num {
            expected = expected.wrapping_add(i);
            let (tx, rx) = oneshot::channel();
            txs.push((i, tx));
            rxs.push(rx);
        }

        let txs = Arc::new(txs);

        for _ in 0..threads {
            let txs = txs.clone();

            thread::spawn(move || {
                while let Some((n, tx)) = txs.pop() {
                    let _ = tx.send(n);
                }
            });
        }

        let result = block_on(future::poll_fn(move |cx| {
            let mut result = 0usize;

            loop {
                if let Poll::Ready(ready) = rxs.poll_next_unpin(cx) {
                    match ready {
                        Some(num) => result = result.wrapping_add(num.unwrap()),
                        None => break,
                    }
                }
            }

            Poll::Ready(expected)
        }));

        assert_eq!(expected, result);
        result
    }
}

criterion_group!(unordered, polling_benchmark);
criterion_main!(unordered);
