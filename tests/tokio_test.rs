use std::time::{Duration, Instant};
use tokio::{stream::StreamExt as _, time};

#[tokio::test]
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
