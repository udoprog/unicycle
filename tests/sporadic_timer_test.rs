use std::time::{Duration, Instant};
use tokio::{stream::StreamExt as _, time};

#[tokio::test(threaded_scheduler)]
async fn test_unicycle_sporadic_timers() {
    use unicycle::FuturesUnordered;

    let mut futures = FuturesUnordered::new();

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
async fn test_futures_sporadic_timers() {
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
