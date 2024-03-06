//! A slab-like, pre-allocated storage where the slab is divided into immovable
//! slots. Each allocated slot doubles the capacity of the slab.
//!
//! Converted from <https://github.com/carllerche/slab>, this slab however
//! contains a growable collection of fixed-size regions called slots.
//! This allows is to store immovable objects inside the slab, since growing the
//! collection doesn't require the existing slots to move.

#![allow(clippy::manual_map)]

use std::pin::Pin;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use crate::shared::Shared;

const MAX_REFCOUNT: usize = (isize::MAX) as usize;

/// Where all tasks and task-related data is stored.
pub(crate) struct Storage<T> {
    /// Shared state across all entries.
    shared: Arc<Shared>,
    /// Entries in the slab.
    ///
    /// Note: We can't use a Box, since we need to access different components
    /// of the entry in different locations, which would not constitute a safe
    /// projection.
    ///
    /// For example, the header of the entry is used inside of the waker being
    /// passed around.
    tasks: Vec<NonNull<Task<T>>>,
    /// The length of the slab.
    len: usize,
    // Offset of the next available slot in the slab.
    next: usize,
}

enum Entry<T> {
    None,
    Some(T),
    Vacant(usize),
}

#[repr(C)]
pub(crate) struct Task<T> {
    header: Header,
    entry: Entry<T>,
}

/// A header is basically a pointer to the shared state combined with the index we wish to poll.
pub(crate) struct Header {
    /// A pointer to the [Shared] task data.
    shared: Arc<Shared>,
    /// The index of the task this waker will wake.
    index: usize,
    /// Reference count of the header.
    reference_count: AtomicUsize,
}

impl Header {
    /// Construct a new waker.
    pub(crate) fn new(shared: Arc<Shared>, index: usize) -> Self {
        Self {
            shared,
            index,
            reference_count: AtomicUsize::new(1),
        }
    }

    /// The index of the task.
    #[inline]
    pub(crate) fn index(&self) -> usize {
        self.index
    }

    /// Access shared storage from header.
    #[inline]
    pub(crate) fn shared(&self) -> &Shared {
        &self.shared
    }

    /// Increment ref count of stored entry.
    pub(crate) fn increment_ref(&self) {
        let count = self.reference_count.fetch_add(1, Ordering::SeqCst);

        // Degenerate case we don't want to support. Any process actually
        // reaching this is already broken to the point of no return since
        // legitimate use would require more than isize::MAX amount of memory.
        if count > MAX_REFCOUNT {
            std::process::abort();
        }
    }

    /// Decrement ref count of stored entry, returns `true` if the entry should be deallocated.
    pub(crate) unsafe fn decrement_ref(&self) -> bool {
        let count = self.reference_count.fetch_sub(1, Ordering::SeqCst);
        count == 1
    }

    /// Deallocate the entry associated with the header.
    pub(crate) unsafe fn deallocate(ptr: NonNull<Header>) {
        let drop_task = ptr.as_ref().shared.drop_task;
        drop_task(ptr.as_ptr().cast_const().cast());
    }
}

impl<T> Storage<T> {
    /// Construct a new, empty [Storage] with the default slot size.
    pub(crate) fn new() -> Self {
        Self {
            shared: Arc::new(Shared::new::<T>()),
            tasks: Vec::new(),
            len: 0,
            next: 0,
        }
    }

    /// Access shared state of the slab.
    pub(crate) fn shared(&self) -> &Arc<Shared> {
        &self.shared
    }

    /// Get the length of the slab.
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Test if the pin slab is empty.
    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Insert a value into the pin slab.
    pub(crate) fn insert(&mut self, val: T) -> usize {
        let key = self.next;
        self.insert_at(key, val);
        key
    }

    /// Access the given key as a pinned mutable value along with its header.
    pub(crate) fn get_pin_mut(&mut self, key: usize) -> Option<(NonNull<Header>, Pin<&mut T>)> {
        let task = *self.tasks.get(key)?;

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            match *ptr::addr_of_mut!((*task.as_ptr()).entry) {
                Entry::Some(ref mut value) => {
                    Some((task.cast::<Header>(), Pin::new_unchecked(value)))
                }
                _ => None,
            }
        }
    }

    /// Get a reference to the value at the given slot.
    #[cfg(test)]
    pub(crate) fn get(&self, key: usize) -> Option<&T> {
        let task = *self.tasks.get(key)?;

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            match *ptr::addr_of!((*task.as_ptr()).entry) {
                Entry::Some(ref value) => Some(value),
                _ => None,
            }
        }
    }

    /// Get a mutable reference to the value at the given slot.
    pub(crate) fn get_mut(&mut self, key: usize) -> Option<&mut T>
    where
        T: Unpin,
    {
        let task = *self.tasks.get(key)?;

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            match *ptr::addr_of_mut!((*task.as_ptr()).entry) {
                Entry::Some(ref mut value) => Some(value),
                _ => None,
            }
        }
    }

    /// Remove the key from the slab.
    ///
    /// Returns `true` if the entry was removed, `false` otherwise.
    /// Removing a key which does not exist has no effect, and `false` will be
    /// returned.
    ///
    /// We need to take care that we don't move it, hence we only perform
    /// operations over pointers below.
    pub(crate) fn remove(&mut self, key: usize) -> bool {
        let task = match self.tasks.get(key) {
            Some(entry) => *entry,
            None => return false,
        };

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            let value = match *ptr::addr_of_mut!((*task.as_ptr()).entry) {
                ref mut value @ Entry::Some(..) => value,
                _ => return false,
            };

            *value = Entry::Vacant(self.next);
        }

        self.len -= 1;
        self.next = key;
        true
    }

    /// Clear all available data in the PinSlot.
    pub(crate) fn clear(&mut self) {
        // SAFETY: We're just decrementing the reference count of each entry
        // before dropping the storage of the slab.
        unsafe {
            for &entry in &self.tasks {
                if entry.as_ref().header.decrement_ref() {
                    // SAFETY: We're the only ones holding a reference to the
                    // entry, so it's safe to drop it.
                    _ = Box::from_raw(entry.as_ptr());
                }
            }

            self.tasks.set_len(0);
        }
    }

    /// Insert a value at the given slot.
    fn insert_at(&mut self, key: usize, value: T) {
        if key >= self.tasks.len() {
            self.tasks.reserve(key - self.tasks.len() + 1);

            for index in self.tasks.len()..=key {
                self.tasks.push(NonNull::from(Box::leak(Box::new(Task {
                    header: Header::new(self.shared.clone(), index),
                    entry: Entry::None,
                }))));
            }
        }

        let task = *self.tasks.get(key).unwrap();

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            self.next = match ptr::addr_of_mut!((*task.as_ptr()).entry).replace(Entry::Some(value))
            {
                Entry::None => key + 1,
                Entry::Vacant(next) => next,
                _ => unreachable!(),
            };

            self.len += 1;
        }
    }
}

impl<T> Default for Storage<T> {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl<T> Send for Storage<T> where T: Send {}
unsafe impl<T> Sync for Storage<T> where T: Sync {}

impl<T> Drop for Storage<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assert_send_sync() {
        fn assert_send<T: Send>(_: &T) {}
        fn assert_sync<T: Sync>(_: &T) {}

        let slab = Storage::<i32>::new();
        assert_send(&slab);
        assert_sync(&slab);

        let _slab = Storage::<std::cell::Cell<i32>>::new();
        // assert_sync(&slab);

        let _slab = Storage::<std::rc::Rc<i32>>::new();
        // assert_send(&slab);
    }

    #[test]
    fn test_basic() {
        let mut slab = Storage::new();

        assert!(!slab.remove(0));
        let index = slab.insert(42);
        assert!(slab.remove(index));
        assert!(!slab.remove(index));
    }

    #[test]
    fn test_new() {
        let mut slab = Storage::new();

        assert!(!slab.remove(0));
        let index = slab.insert(42);
        assert!(slab.remove(index));
        assert!(!slab.remove(index));
    }

    #[test]
    fn test_len() {
        let mut slab = Storage::new();
        assert_eq!(0, slab.len());
        assert_eq!(0, slab.insert(42));
        assert_eq!(1, slab.len());
    }

    #[test]
    fn test_is_empty() {
        let mut slab = Storage::new();
        assert!(slab.is_empty());
        assert_eq!(0, slab.insert(42));
        assert!(!slab.is_empty());
    }

    #[test]
    fn test_get() {
        let mut slab = Storage::new();
        let key = slab.insert(42);
        assert_eq!(Some(&42), slab.get(key));
    }

    #[test]
    fn test_get_mut() {
        let mut slab = Storage::new();
        let key = slab.insert(42);
        *slab.get_mut(key).unwrap() = 43;
        assert_eq!(Some(&43), slab.get(key));
    }

    #[test]
    fn test_remove() {
        let mut slab = Storage::new();

        assert!(!slab.remove(0));
        let index = slab.insert(42);
        assert!(slab.remove(index));
        assert!(!slab.remove(index));
    }

    #[test]
    fn test_clear() {
        let mut slab = Storage::new();
        assert_eq!(0, slab.insert(42));
        slab.clear();
        assert!(slab.get(0).is_none());
    }
}
