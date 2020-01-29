use std::time::{Duration, Instant};
use tokio::{stream::StreamExt as _, time};

#[tokio::test(threaded_scheduler)]
async fn test_bitset() {
    use unicycle::Unordered;

    let mut futures = Unordered::new();

    for _ in 0..1_000 {
        futures.push(time::delay_for(Duration::from_millis(
            100 + (rand::random::<f32>() * 100f32) as u64,
        )));
    }

    let start = Instant::now();

    while let Some(_) = futures.next().await {}

    println!("bitset: {:?}", Instant::now().duration_since(start));
}

#[tokio::test]
async fn test_futures() {
    use futures::stream::FuturesUnordered;

    let mut futures = FuturesUnordered::new();

    for _ in 0..1_000 {
        futures.push(time::delay_for(Duration::from_millis(
            100 + (rand::random::<f32>() * 100f32) as u64,
        )));
    }

    let start = Instant::now();

    while let Some(_) = futures.next().await {}

    println!("futures: {:?}", Instant::now().duration_since(start));
}

#[tokio::test]
async fn test_unicycle_streams() {
    use tokio::stream::{iter, StreamExt as _};
    use unicycle::Unordered;

    let mut streams = Unordered::streams();
    assert!(streams.is_empty());

    streams.push(iter(vec![1, 2, 3, 4]));
    streams.push(iter(vec![5, 6, 7, 8]));

    let mut received = Vec::new();

    while let Some(value) = streams.next().await {
        received.push(value);
    }

    assert_eq!(vec![1, 5, 2, 6, 3, 7, 4, 8], received);
}
