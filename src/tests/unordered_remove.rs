use std::future::ready;

use futures::FutureExt;

use crate::FuturesUnordered;

#[test]
fn test_remove() {
    let mut futures = FuturesUnordered::new();
    let index = futures.push(ready(42));

    assert_eq!(futures.len(), 1);

    let removed = futures.remove(index);
    assert!(removed.is_some());
    assert_eq!(futures.len(), 0);

    assert!(futures.remove(index).is_none());
    assert!(futures.remove(0).is_none());
    assert!(futures.remove(999).is_none());
}

#[tokio::test]
async fn test_complete_unpinned() {
    let mut futures = FuturesUnordered::new();

    futures.push(Box::pin(ready(1)));
    futures.push(Box::pin(ready(2)));
    let idx = futures.push(Box::pin(ready(3)));
    futures.push(Box::pin(ready(4)));

    let fut = futures.remove(idx).unwrap();

    let mut res = vec![];
    while let Some(x) = futures.next().await {
        res.push(x);
    }
    res.sort();
    assert_eq!(res, vec![1, 2, 4]);
    assert_eq!(fut.await, 3);
}

#[tokio::test]
async fn test_manual_poll_then_remove() {
    let mut futures = FuturesUnordered::new();

    let fut = std::future::ready(123);
    let idx = futures.push(fut);

    let res = futures.get_pin_mut(idx).unwrap().now_or_never();
    assert!(res.is_some());

    let _fut = futures.remove(idx).unwrap();

    let res = futures.next().now_or_never();
    assert_eq!(res, Some(None));
    assert!(futures.is_empty());
}
