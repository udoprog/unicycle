# unicycle

[![Documentation](https://docs.rs/unicycle/badge.svg)](https://docs.rs/unicycle)
[![Crates](https://img.shields.io/crates/v/unicycle.svg)](https://crates.io/crates/unicycle)
[![Actions Status](https://github.com/udoprog/unicycle/workflows/Rust/badge.svg)](https://github.com/udoprog/unicycle/actions)

A scheduler for driving a large number of futures.

Unicycle provides the [Unordered] type, which is a futures abstraction that
runs a set of futures which may complete in any order.
Similarly to [FuturesUnordered].
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

## Fairness

You can think of abstractions like Unicycle as schedulers. They are provided a
set of child tasks, and try to do their best to drive them to completion. In
this regard, it's interesting to talk about _fairness_ in how the tasks are
being driven.

The current implementation of [FuturesUnordered] maintains a queue of tasks
interested in waking up. As a task is woken up, it's added to the head of this
queue to signal its interest. When [FuturesUnordered] is being polled, it
checks the head of this queue in a loop. As long as there is a task interested
in being woken up, this task will be polled. This procuedure has the side effect
of tasks which aggressively signal interest in waking up, will receive priority
and be polled more frequently.

This process can lead to an especially unfortunate cases where a small number of
tasks can can cause the polling loop of [FuturesUnordered] to
[spin abnormally].
This issue was [reported by Jon Gjengset], and improved on by [limiting the
amount FuturesUnordered is allowed to spin].

Unicycle addresses this by limiting how frequently a child task may be polled
per _polling cycle_. This is done by keeping two sets of polling interest and
atomically swapping it out once we are polling, then taking the swapped out set
and use as a basis for what to poll in order, but only _once_. Additional
wakeups are only registered in the swapped in set which will be polled the next
cycle. For more details, see the _Architecture_ section below.

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

[slab]: https://github.com/carllerche/slab
[pin API]: https://doc.rust-lang.org/std/pin/index.html

Next to the slab we maintain two bitsets, one _active_ and one _alternate_.
When a task registers interest in waking up, the bit associated with its index
is set in the active set, and the latest waker passed into [Unordered] is
called to wake it up.
Once [Unordered] is polled, it atomically swaps the active and alternate
bitsets, waits until it has exclusive access to the now _alternate_ bitset, and
drains it from all the indexes which have been flagged to determine which tasks
to poll.
Each task is then polled _once_ in order.
If the task is [Ready], its result is added to a result queue.

[Ready]: https://doc.rust-lang.org/std/task/enum.Poll.html

Unicycle now prioritizes draining the result queue above everything else. Once
it is empty, we start the cycle over again.

[PinSlab]: https://docs.rs/unicycle/latest/unicycle/struct.PinSlab.html
[Slab]: https://docs.rs/slab/latest/slab/struct.Slab.html
[Unordered]: https://docs.rs/unicycle/latest/unicycle/struct.Unordered.html
[FuturesUnordered]: https://docs.rs/futures/latest/futures/stream/struct.FuturesUnordered.html