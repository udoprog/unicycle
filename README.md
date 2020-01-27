# unicycle

**Note:** This project is experimental. It involves a large amount of unsafe
and possibly bad assumptions which needs to be either vetted or removed before
you should consider putting it in production.

Unicycle provides an implementation of `FuturesUnordered` aimed to be _fairer_.
Easier to implement. And store the futures being polled in a way which provides
for better memory locality.

## Features

* `parking-lot` - To enable locking using the [parking_lot] crate (optional).

## Fairness

The current implementation of `FuturesUnordered` maintains a queue of tasks
interested in waking up. As a task is woken up, it's added to the head of this
queue.

This process is run in a loop during poll, which will dequeue the next task to
poll. This can lead to a fair bit of unfairness, since tasks which agressively
signal interest in waking up will receive priority in being polled. In
particular - a task which calls `wake_by_ref` and returns a `Poll::Pending`
will cause the `FuturesUnordered` to [spin indefinitely]. This issue was
[reported by Jon Gjengset].

The following is explained in greater detail in the next section. But we achieve
fairness by limiting the number of polls any future can have to one per cycle.
And we make this efficient by maintaining this set of futures to poll in bitsets
tracking wakeup interest, which we atomically cycle between.

[spin indefinitely]: https://github.com/udoprog/unicycle/blob/master/tests/spinning_futures_unordered.rs
[reported by Jon Gjengset]: https://github.com/rust-lang/futures-rs/issues/2047

## Architecture

The `Unordered` type stores all futures being polled in a `PinSlab` (See [slab]
for details, but note that `PinSlab` provides a similar API but differently).
This maintains a growable collection of fixed-size memory regions, allowing it
to store immovable objects. The primary feature of a slab is that it
automatically reclaims memory at low cost. Each future inserted into the slab is
assigned an _index_.

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
* ~~Either remove lock in `SharedWaker` (`ArcSwap::swap` might block), or switch
  to a variant which can suspend the current task.~~
* ~~Either remove lock in `SharedWakeSet`, or switch to a variant which can
  suspend the current task.~~
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