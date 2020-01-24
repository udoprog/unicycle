use futures::channel::oneshot;
use futures::future;
use futures::stream::StreamExt;
use futures::task::Poll;
use std::collections::VecDeque;
use std::thread;

const NUM: usize = 10_000;
const EXPECTED: usize = 50005000;

#[tokio::test]
async fn oneshots_unicycle() {
    use unicycle::Unordered;

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

    future::poll_fn(move |cx| {
        let mut count = 0;
        let mut result = 0usize;

        loop {
            if let Poll::Ready(Some(Ok(num))) = rxs.poll_next_unpin(cx) {
                count += 1;
                result = result.wrapping_add(num);

                if count == NUM {
                    break;
                }
            }
        }

        assert_eq!(EXPECTED, result);
        Poll::Ready(())
    })
    .await;
}
