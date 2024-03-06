use std::mem;
use std::ptr;
use std::task::{Context, Poll};

use uniset::BitSet;

use crate::task::Task;
use crate::wake_set::{SharedWakeSet, WakeSet};
use crate::waker::SharedWaker;

/// Data that is shared across all sub-tasks.
pub(crate) struct Shared {
    /// The currently registered parent waker.
    pub(crate) waker: SharedWaker,
    /// The currently registered wake set.
    pub(crate) wake_set: SharedWakeSet,
    /// Function to use when dropping a task from a header, since the header is
    /// unaware of the layout of the task.
    pub(crate) drop_task: unsafe fn(*const ()),
}

impl Shared {
    /// Construct new shared data.
    pub(crate) fn new<T>() -> Self {
        unsafe fn drop_task<T>(ptr: *const ()) {
            _ = Box::from_raw(ptr.cast_mut().cast::<Task<T>>());
        }

        Self {
            waker: SharedWaker::new(),
            wake_set: SharedWakeSet::new(),
            drop_task: drop_task::<T>,
        }
    }

    /// Swap the active wake set with the alternate one.
    /// Also makes sure that the capacity of the active bitset is updated if the
    /// alternate one has.
    ///
    /// # Safety
    ///
    /// Caller must be assured that they are the only one who is attempting to
    /// swap out the wake sets.
    pub(crate) unsafe fn poll_swap_active<'a>(
        &self,
        cx: &Context<'_>,
        alternate: &mut *mut WakeSet,
    ) -> Poll<(bool, &'a mut BitSet)> {
        let non_empty = {
            let alternate = (**alternate).as_mut_set();
            let non_empty = !alternate.is_empty();

            // We always force a swap if the capacity has changed, because then
            // we expect subtasks to poll the swapped in set since they were
            // newly added.
            if non_empty {
                return Poll::Ready((true, alternate));
            }

            // Note: We must swap the waker before we swap the set.
            if !self.waker.swap(cx.waker()) {
                return Poll::Pending;
            }

            non_empty
        };

        let wake_set = self.swap_active(alternate);
        Poll::Ready((non_empty, wake_set))
    }

    /// Perform a swap of the active sets. This is safe, because we perform the
    /// appropriate locking while swapping the sets.
    ///
    /// # Safety
    ///
    /// We must ensure that we have unique access to the alternate set being
    /// swapped.
    pub(crate) unsafe fn swap_active<'a>(&self, alternate: &mut *mut WakeSet) -> &'a mut BitSet {
        // Unlock. At this position, if someone adds an element to the wake set
        // they are also bound to call wake, which will cause us to wake up.
        //
        // There is a race going on between locking and unlocking, and it's
        // beneficial for child tasks to observe the locked state of the wake
        // set so they refetch the other set instead of having to wait until
        // another wakeup.
        (**alternate).unlock_exclusive();

        let next = mem::replace(alternate, ptr::null_mut());
        debug_assert!(!next.is_null());

        *alternate = self.wake_set.swap(next);

        // Make sure no one else is using the alternate wake.
        //
        // Safety: We are the only one swapping alternate, so at
        // this point we know that we have access to the most recent
        // active set. We _must_ call lock_exclusive before we
        // can punt this into a mutable reference though, because at
        // this point inner futures will still have access to references
        // to it (under a lock!). We must wait for these to expire.
        //
        // We also unfortunately can't yield here, because we've swapped the
        // alternate set which could be used when pushing to the set.
        (**alternate).lock_exclusive();

        // Safety: While this is live we must _not_ mess with
        // `alternate` in any way.
        (**alternate).as_mut_set()
    }
}

unsafe impl Send for Shared {}
unsafe impl Sync for Shared {}
