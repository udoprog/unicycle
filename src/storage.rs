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
use std::sync::Arc;

use crate::waker::Header;
use crate::Shared;

/// Pre-allocated storage for a uniform data type, with slots of immovable
/// memory regions.
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
    entries: Vec<NonNull<Entry<T>>>,
    /// The length of the slab.
    len: usize,
    // Offset of the next available slot in the slab.
    next: usize,
}

#[repr(C)]
pub(crate) struct Entry<T> {
    header: Header,
    vacant: Option<usize>,
    value: Option<T>,
}

impl<T> Storage<T> {
    /// Construct a new, empty [Storage] with the default slot size.
    pub(crate) fn new() -> Self {
        Self {
            shared: Arc::new(Shared::new::<T>()),
            entries: Vec::new(),
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
        let entry = *self.entries.get(key)?;

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            match &mut *ptr::addr_of_mut!((*entry.as_ptr()).value) {
                Some(value) => Some((entry.cast::<Header>(), Pin::new_unchecked(value))),
                None => None,
            }
        }
    }

    /// Get a reference to the value at the given slot.
    #[cfg(test)]
    pub(crate) fn get(&self, key: usize) -> Option<&T> {
        let entry = *self.entries.get(key)?;

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe { (*ptr::addr_of!((*entry.as_ptr()).value)).as_ref() }
    }

    /// Get a mutable reference to the value at the given slot.
    pub(crate) fn get_mut(&mut self, key: usize) -> Option<&mut T>
    where
        T: Unpin,
    {
        let entry = *self.entries.get(key)?;

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe { (*ptr::addr_of_mut!((*entry.as_ptr()).value)).as_mut() }
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
        let entry = match self.entries.get(key) {
            Some(entry) => *entry,
            None => return false,
        };

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            match ptr::addr_of_mut!((*entry.as_ptr()).value).replace(None) {
                Some(..) => (),
                _ => return false,
            }

            ptr::addr_of_mut!((*entry.as_ptr()).vacant).write(Some(self.next));
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
            for &entry in &self.entries {
                if entry.as_ref().header.decrement_ref() {
                    // SAFETY: We're the only ones holding a reference to the
                    // entry, so it's safe to drop it.
                    _ = Box::from_raw(entry.as_ptr());
                }
            }

            self.entries.set_len(0);
        }
    }

    /// Insert a value at the given slot.
    fn insert_at(&mut self, key: usize, val: T) {
        if key >= self.entries.len() {
            self.entries.reserve(key - self.entries.len() + 1);

            for index in self.entries.len()..=key {
                self.entries.push(NonNull::from(Box::leak(Box::new(Entry {
                    header: Header::new(self.shared.clone(), index),
                    vacant: None,
                    value: None,
                }))));
            }
        }

        let entry = *self.entries.get(key).unwrap();

        // SAFETY: We have mutable access to the given entry, but we are careful
        // not to dereference the header mutably, since that might be shared.
        unsafe {
            self.next = match ptr::addr_of_mut!((*entry.as_ptr()).vacant).replace(None) {
                None => key + 1,
                Some(next) => next,
            };

            let existing = ptr::addr_of_mut!((*entry.as_ptr()).value).replace(Some(val));
            assert!(existing.is_none(), "Entry already occupied");
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
