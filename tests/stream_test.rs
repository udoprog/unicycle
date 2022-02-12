use tokio_stream::iter;
use unicycle::StreamsUnordered;

#[tokio::test]
async fn test_unicycle_streams() {
    let mut streams = StreamsUnordered::new();
    assert!(streams.is_empty());

    streams.push(iter(vec![1, 2, 3, 4]));
    streams.push(iter(vec![5, 6, 7, 8]));

    let mut received = Vec::new();

    while let Some(value) = streams.next().await {
        received.push(value);
    }

    assert_eq!(vec![5, 1, 6, 2, 7, 3, 8, 4], received);
}
