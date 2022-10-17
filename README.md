# unicycle

[<img alt="github" src="https://img.shields.io/badge/github-udoprog/unicycle-8da0cb?style=for-the-badge&logo=github" height="20">](https://github.com/udoprog/unicycle)
[<img alt="crates.io" src="https://img.shields.io/crates/v/unicycle.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/unicycle)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-unicycle-66c2a5?style=for-the-badge&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">](https://docs.rs/unicycle)
[<img alt="build status" src="https://img.shields.io/github/workflow/status/udoprog/unicycle/CI/main?style=for-the-badge" height="20">](https://github.com/udoprog/unicycle/actions?query=branch%3Amain)

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

<br>

## Features

* `parking-lot` - To enable locking using the [parking_lot] crate (default).
* `futures-rs` - Enable the used of the Stream type from [futures-rs].
  This is required to get access to [StreamsUnordered] and
  [IndexedStreamsUnordered] since these wrap over [futures-rs] types. (default)

<br>

## Examples

```no_miri
use tokio::time;
use std::time::Duration;
use unicycle::FuturesUnordered;

#[tokio::main]
async fn main() {
    let mut futures = FuturesUnordered::new();

    futures.push(time::sleep(Duration::from_secs(2)));
    futures.push(time::sleep(Duration::from_secs(3)));
    futures.push(time::sleep(Duration::from_secs(1)));

    while let Some(_) = futures.next().await {
        println!("tick");
    }

    println!("done!");
}
```

[Unordered] types can be created from iterators:

```no_miri
use tokio::time;
use std::time::Duration;
use unicycle::FuturesUnordered;

#[tokio::main]
async fn main() {
    let mut futures = Vec::new();

    futures.push(time::sleep(Duration::from_secs(2)));
    futures.push(time::sleep(Duration::from_secs(3)));
    futures.push(time::sleep(Duration::from_secs(1)));

    let mut futures = futures.into_iter().collect::<FuturesUnordered<_>>();

    while let Some(_) = futures.next().await {
        println!("tick");
    }

    println!("done!");
}
```

<br>

## Fairness

You can think of abstractions like Unicycle as schedulers. They are provided
a set of child tasks, and try to do their best to drive them to completion.
In this regard, it's interesting to talk about _fairness_ in how the tasks
are being driven.

The current implementation of [FuturesUnordered][futures-rs] maintains a
queue of tasks interested in waking up. As a task is woken up it's added to
the head of this queue to signal its interest in being polled. When
[FuturesUnordered][futures-rs] works it drains this queue in a loop and
polls the associated task. This process has a side effect where tasks who
aggressively signal interest in waking up will receive priority and be
polled more frequently. Since there is a higher chance that while the queue
is being drained, their interest will be re-added at the head of the queue
immeidately. This can lead to instances where a small number of tasks can
can cause the polling loop of [FuturesUnordered][futures-rs] to [spin
abnormally]. This issue was [reported by Jon Gjengset] and is improved on by
[limiting the amount FuturesUnordered is allowed to spin].

Unicycle addresses this by limiting how frequently a child task may be
polled per _polling cycle_. This is done by tracking polling interest in two
separate sets. Once we are polled, we swap out the active set then take the
swapped out set and use as a basis for what to poll in order while limiting
ourselves to only poll _once_ per child task. Additional wakeups are only
registered in the swapped in set which will be polled the next cycle.

This way we hope to achieve a higher degree of fairness, never favoring the
behavior of one particular task.

<br>

## Architecture

The [Unordered] type stores all futures being polled in a [PinSlab]
(Inspired by the [slab] crate). A slab is capable of utomatically reclaiming
storage at low cost, and will maintain decent memory locality. A [PinSlab]
is different from a [Slab] in how it allocates the memory regions it uses to
store objects. While a regular [Slab] is simply backed by a vector which
grows as appropriate, this approach is not viable for pinning, since it
would cause the objects to move while being reallocated. Instead [PinSlab]
maintains a growable collection of fixed-size memory regions, allowing it to
store and reference immovable objects through the [pin API]. Each future
inserted into the slab is assigned an _index_, which we will be using below.
We now call the inserted future a _task_, and you can think of this index as
a unique task identifier.

Next to the slab we maintain two [BitSets][BitSet], one _active_ and one
_alternate_. When a task registers interest in waking up, the bit associated
with its index is set in the active set, and the latest waker passed into
[Unordered] is called to wake it up. Once [Unordered] is polled, it
atomically swaps the active and alternate [BitSets][BitSet], waits until it
has exclusive access to the now _alternate_ [BitSet], and drains it from all
the indexes which have been flagged to determine which tasks to poll. Each
task is then polled _once_ in order. If the task is [Ready], its result is
yielded. After we receive control again, we continue draining the alternate
set in this manner, until it is empty. When this is done we yield once, then
we start the cycle over again.

[BitSet]: https://docs.rs/uniset/latest/uniset/struct.BitSet.html
[futures crate]: https://docs.rs/futures/latest/futures
[futures-rs]: https://crates.io/crates/futures
[futures-rs]: https://docs.rs/futures/latest/futures/stream/struct.FuturesUnordered.html
[FuturesUnordered]: https://docs.rs/unicycle/latest/unicycle/type.FuturesUnordered.html
[IndexedStreamsUnordered]: https://docs.rs/unicycle/latest/unicycle/type.IndexedStreamsUnordered.html
[limiting the amount FuturesUnordered is allowed to spin]: https://github.com/rust-lang/futures-rs/pull/2049
[parking_lot]: https://crates.io/crates/parking_lot
[pin API]: https://doc.rust-lang.org/std/pin/index.html
[PinSlab]: https://docs.rs/unicycle/latest/unicycle/pin_slab/struct.PinSlab.html
[Ready]: https://doc.rust-lang.org/std/task/enum.Poll.html
[reported by Jon Gjengset]: https://github.com/rust-lang/futures-rs/issues/2047
[Slab]: https://docs.rs/slab/latest/slab/struct.Slab.html
[slab]: https://github.com/carllerche/slab
[spin abnormally]: https://github.com/udoprog/unicycle/blob/main/tests/spinning_futures_unordered_test.rs
[StreamsUnordered]: https://docs.rs/unicycle/latest/unicycle/type.StreamsUnordered.html
[Unordered]: https://docs.rs/unicycle/latest/unicycle/struct.Unordered.html
