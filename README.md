# unicycle

[![Documentation](https://docs.rs/unicycle/badge.svg)](https://docs.rs/unicycle)
[![Crates](https://img.shields.io/crates/v/unicycle.svg)](https://crates.io/crates/unicycle)
[![Actions Status](https://github.com/udoprog/unicycle/workflows/Rust/badge.svg)](https://github.com/udoprog/unicycle/actions)

A scheduler for driving a large number of futures.


Unicycle provides a collection of [Unordered] types:
 
 * [FuturesUnordered]
 * [StreamsUnordered]
 * [IndexedStreamsUnordered]
 
These are async abstractions that runs a set of futures or streams which may
complete in any order.
Similarly to [FuturesUnordered][futures-rs] from the [futures crate].

But we aim to provide a stronger guarantee of fairness (see below), and
better memory locality for the futures being pollled.

**Note:** This project is experimental. It involves some amount of unsafe and
possibly bad assumptions which needs to be either vetted or removed before you
should consider putting it in production.

## Features

* `parking-lot` - To enable locking using the [parking_lot] crate (optional).
* `vec-safety` - Avoid relying on the assumption that `&mut Vec<T>` can be
  safely coerced to `&mut Vec<U>` if `T` and `U` have an identical memory
  layouts (enabled by default, [issue #1]).

[issue #1]: https://github.com/udoprog/unicycle/issues/1
[parking_lot]: https://crates.io/crates/parking_lot

## Examples

```rust
use tokio::{stream::StreamExt as _, time};
use std::time::Duration;
use unicycle::FuturesUnordered;

#[tokio::main]
async fn main() {
    let mut futures = FuturesUnordered::new();

    futures.push(time::delay_for(Duration::from_secs(2)));
    futures.push(time::delay_for(Duration::from_secs(3)));
    futures.push(time::delay_for(Duration::from_secs(1)));

    while let Some(_) = futures.next().await {
        println!("tick");
    }

    println!("done!");
}
```

[Unordered] types can be created from iterators:

```rust
use tokio::{stream::StreamExt as _, time};
use std::time::Duration;
use unicycle::FuturesUnordered;

#[tokio::main]
async fn main() {
    let mut futures = Vec::new();

    futures.push(time::delay_for(Duration::from_secs(2)));
    futures.push(time::delay_for(Duration::from_secs(3)));
    futures.push(time::delay_for(Duration::from_secs(1)));

    let mut futures = futures.into_iter().collect::<FuturesUnordered<_>>();

    while let Some(_) = futures.next().await {
        println!("tick");
    }

    println!("done!");
}
```

## Fairness

You can think of abstractions like Unicycle as schedulers. They are provided a
set of child tasks, and try to do their best to drive them to completion. In
this regard, it's interesting to talk about _fairness_ in how the tasks are
being driven.

The current implementation of [FuturesUnordered][futures-rs] maintains a queue
of tasks interested in waking up. As a task is woken up, it's added to the head
of this queue to signal its interest.
When [FuturesUnordered][futures-rs] is being polled, it drains this queue in a
loop and polls the associated task.
This process has a side effect of tasks who aggressively signal interest in
waking up will receive priority and be polled more frequently, since there is a
higher chance that while the queue is being drained, their interest will be
re-added to the queue.
This can lead to instances where a small number of tasks can can cause the 
polling loop of [FuturesUnordered][futures-rs] to [spin abnormally].
This issue was [reported by Jon Gjengset], and improved on by [limiting the
amount FuturesUnordered is allowed to spin].

Unicycle addresses this by limiting how frequently a child task may be polled
per _polling cycle_.
This is done by tracking polling intrest in two separate sets.
Once we are polled, we swap out the active set, then take the swapped out set
and use as a basis for what to poll in order, but we limit ourselves to only
poll _once_ per child task.
Additional wakeups are only registered in the swapped in set which will be
polled the next cycle.

This way we hope to achieve a higher degree of fairness, never favoring the
behavior of one particular task.

[spin abnormally]: https://github.com/udoprog/unicycle/blob/master/tests/spinning_futures_unordered.rs
[limiting the amount FuturesUnordered is allowed to spin]: https://github.com/rust-lang/futures-rs/pull/2049
[reported by Jon Gjengset]: https://github.com/rust-lang/futures-rs/issues/2047

## Architecture

The Unordered type stores all futures being polled in a [PinSlab] (Inspired by
the [slab] crate).
A slab is capable of utomatically reclaiming storage at low cost, and will
maintain decent memory locality.
A [PinSlab] is different from a [Slab] in how it allocates the memory regions it
uses to store objects.
While a regular [Slab] is simply backed by a vector which grows as appropriate,
this approach is not viable for pinning, since it would cause the objects to
move while being reallocated.
Instead [PinSlab] maintains a growable collection of fixed-size memory regions,
allowing it to store and reference immovable objects through the [pin API].
Each future inserted into the slab is assigned an _index_, which we will be
using below.
We now call the inserted future a _task_, and you can think of this index as a
unique task identifier.

Next to the slab we maintain two [bit sets], one _active_ and one _alternate_.
When a task registers interest in waking up, the bit associated with its index
is set in the active set, and the latest waker passed into [Unordered] is called
to wake it up.
Once [Unordered] is polled, it atomically swaps the active and alternate
[bit sets], waits until it has exclusive access to the now _alternate_ [BitSet],
and drains it from all the indexes which have been flagged to determine which
tasks to poll.
Each task is then polled _once_ in order.
If the task is [Ready], its result is yielded.
After we receive control again, we continue draining the alternate set in this
manner, until it is empty.
When this is done we yield once, then we start the cycle over again.

[slab]: https://github.com/carllerche/slab
[pin API]: https://doc.rust-lang.org/std/pin/index.html
[Ready]: https://doc.rust-lang.org/std/task/enum.Poll.html
[PinSlab]: https://docs.rs/unicycle/latest/unicycle/pin_slab/struct.PinSlab.html
[Slab]: https://docs.rs/slab/latest/slab/struct.Slab.html
[FuturesUnordered]: https://docs.rs/unicycle/latest/unicycle/type.FuturesUnordered.html
[StreamsUnordered]: https://docs.rs/unicycle/latest/unicycle/type.StreamsUnordered.html
[IndexedStreamsUnordered]: https://docs.rs/unicycle/latest/unicycle/type.IndexedStreamsUnordered.html
[Unordered]: https://docs.rs/unicycle/latest/unicycle/struct.Unordered.html
[futures-rs]: https://docs.rs/futures/latest/futures/stream/struct.FuturesUnordered.html
[futures crate]: https://docs.rs/futures/latest/futures
[bit sets]: https://docs.rs/uniset/latest/uniset/struct.BitSet.html
[BitSet]: https://docs.rs/uniset/latest/uniset/struct.BitSet.html