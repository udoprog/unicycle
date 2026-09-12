//! Dropping a container whose futures panic in `Drop` must not revisit tasks
//! that have already been deallocated.
//!
//! `Unordered::drop` clears the slab, and `Drop for Storage` clears it again.
//! An unwind out of the first pass used to leave the task vector pointing at
//! freed allocations, which the second pass then dereferenced.

use std::future::Future;
use std::panic::{self, AssertUnwindSafe};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::task::{Context, Poll};

use unicycle::FuturesUnordered;

static DROPS: AtomicUsize = AtomicUsize::new(0);
// Only panic once. A second panic while unwinding would abort the process
// before any tooling gets to report.
static FIRED: AtomicBool = AtomicBool::new(false);

struct Bomb {
    id: usize,
    heap: String,
}

impl Future for Bomb {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        Poll::Pending
    }
}

impl Drop for Bomb {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
        // Deliberately not the first task: the panic has to land after at
        // least one task has been freed, or the second pass has nothing
        // dangling to walk.
        assert!(!self.heap.is_empty());

        if self.id == 3 && !FIRED.swap(true, Ordering::SeqCst) {
            panic!("boom");
        }
    }
}

#[test]
fn panicking_drop_does_not_revisit_freed_tasks() {
    let mut futures = FuturesUnordered::new();

    for id in 0..8 {
        futures.push(Bomb {
            id,
            heap: "x".repeat(64),
        });
    }

    let hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let result = panic::catch_unwind(AssertUnwindSafe(move || drop(futures)));
    panic::set_hook(hook);

    assert!(result.is_err(), "expected the bomb to unwind");

    // Every task is dropped exactly once: 0 through 3 before the unwind, the
    // rest by the guard on the way out.
    assert_eq!(DROPS.load(Ordering::SeqCst), 8);
}
