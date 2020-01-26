# unicycle

**Note:** This project is experimental. It involves a large amount of unsafe
and possibly bad assumptions which needs to be either vetted or removed before
you should consider putting it in production.

This provides an experimental variant of `FuturesUnordered` aimed to be
_fairer_. Easier to maintain, and store the futures being polled in a way which
provides better memory locality.

## Architecture

The `Unordered` type stores all futures being polled in a `PinSlab` (See [slab]
for details, all though note that `PinSlab` is different). This maintains a
growable collection of fixed-size memory regions, allowing it to store immovable
objects. The primary feature of a slab is that it automatically reclaims memory
at low cost. Each future inserted into the slab is assigned an _index_.

Next to the futures we maintain two bitsets, one _active_ and one
_alternate_. When a future is woken up, the bit associated with its index is
set in the active set, and the waker associated with the poll to `Unordered`
is called.

Once `Unordered` is polled, it atomically swaps the active and alternate
bitsets, waits until it has exclusive access to the now _alternate_ bitset, and
drains it from all the indexes which have been flagged to determine which
futures to poll.

We can also add futures to `Unordered`, this is achieved by inserting it into
the slab, then marking that index in a special `pollable` collection that it
should be polled the next time `Unordered` is.

[slab]: https://github.com/carllerche/slab

## TODO

* ~~Build our own sparse atomic bitset. We know exactly how many futures will
  ever touch any given bitset that is swapped in. That allows us to
  pre-allocate - or grow to - exactly as much space as we need.~~
* Either remove lock in `SharedWaker` (`ArcSwap::swap` might block), or switch
  to a variant which can suspend the current task.
* Either remove lock in `SharedWakeSet`, or switch to a variant which can
  suspend the current task.
* Reduce unsafe use. Some of it exists because we didn't want to change the API
  too much when switching away from hibitset.

## Examples

```rust
use tokio::{stream::StreamExt as _, time};
use std::time::Duration;

#[tokio::main]
async fn main() {
    let mut futures = unicycle::Unordered::new();

    futures.push(time::delay_for(Duration::from_secs(2)));
    futures.push(time::delay_for(Duration::from_secs(3)));
    futures.push(time::delay_for(Duration::from_secs(1)));

    while let Some(_) = futures.next().await {
        println!("tick");
    }

    println!("done!");
}
```