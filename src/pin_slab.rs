//! A slab-like, pre-allocated storage where the slab is divided into immovable
//! slots. Each allocated slot doubles the capacity of the slab.
//!
//! Converted from <https://github.com/carllerche/slab>, this slab however
//! contains a growable collection of fixed-size regions called slots.
//! This allows is to store immovable objects inside the slab, since growing the
//! collection doesn't require the existing slots to move.
//!
//! # Examples
//!
//! ```rust
//! use unicycle::pin_slab::PinSlab;
//!
//! let mut slab = PinSlab::new();
//!
//! assert!(!slab.remove(0));
//! let index = slab.insert(42);
//! assert!(slab.remove(index));
//! assert!(!slab.remove(index));
//! ```

use std::pin::Pin;

use pin_project::pin_project;

use crate::pin_vec::PinVec;

/// Pre-allocated storage for a uniform data type, with slots of immovable
/// memory regions.
///
/// ## `Sync` and `Send` Auto Traits
///
/// `PinSlab<T>` is `Sync` or `Send` if `T` is. Examples:
///
/// `Send` and `Sync`:
/// ```
/// # use unicycle::pin_slab::PinSlab;
/// fn assert_send<T: Send>(_: &T) {}
/// fn assert_sync<T: Sync>(_: &T) {}
///
/// let slab = PinSlab::<i32>::new();
/// assert_send(&slab);
/// assert_sync(&slab);
/// ```
///
/// `!Sync`:
/// ```compile_fail
/// # use unicycle::pin_slab::PinSlab;
/// # fn assert_sync<T: Sync>(_: &T) {}
///
/// let slab = PinSlab::<std::cell::Cell<i32>>::new();
/// assert_sync(&slab);
/// ```
///
/// `!Send`:
/// ```compile_fail
/// # use unicycle::pin_slab::PinSlab;
/// # fn assert_send<T: Send>(_: &T) {}
///
/// let slab = PinSlab::<std::rc::Rc<i32>>::new();
/// assert_send(&slab);
/// ```
pub struct PinSlab<T> {
    entries: PinVec<Entry<T>>,
    len: usize,
    // Offset of the next available slot in the slab.
    next: usize,
}

#[pin_project(project = EntryProject)]
enum Entry<T> {
    // Each slot is pre-allocated with entries of `None`.
    None,
    // Removed entries are replaced with the vacant tomb stone, pointing to the
    // next vacant entry.
    Vacant(usize),
    // An entry that is occupied with a value.
    Occupied(#[pin] T),
}

impl<T> PinSlab<T> {
    /// Construct a new, empty [PinSlab] with the default slot size.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::pin_slab::PinSlab;
    ///
    /// let mut slab = PinSlab::new();
    ///
    /// assert!(!slab.remove(0));
    /// let index = slab.insert(42);
    /// assert!(slab.remove(index));
    /// assert!(!slab.remove(index));
    /// ```
    pub fn new() -> Self {
        Self {
            entries: PinVec::new(),
            len: 0,
            next: 0,
        }
    }

    /// Get the length of the slab.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::pin_slab::PinSlab;
    ///
    /// let mut slab = PinSlab::new();
    /// assert_eq!(0, slab.len());
    /// assert_eq!(0, slab.insert(42));
    /// assert_eq!(1, slab.len());
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Test if the pin slab is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::pin_slab::PinSlab;
    ///
    /// let mut slab = PinSlab::new();
    /// assert!(slab.is_empty());
    /// assert_eq!(0, slab.insert(42));
    /// assert!(!slab.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Insert a value into the pin slab.
    pub fn insert(&mut self, val: T) -> usize {
        let key = self.next;
        self.insert_at(key, val);
        key
    }

    /// Access the given key as a pinned mutable value.
    pub fn get_pin_mut(&mut self, key: usize) -> Option<Pin<&mut T>> {
        self.entries
            .get_pin_mut(key)
            .and_then(|entry| match entry.project() {
                EntryProject::Occupied(entry) => Some(entry),
                _ => None,
            })
    }

    /// Get a reference to the value at the given slot.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::pin_slab::PinSlab;
    ///
    /// let mut slab = PinSlab::new();
    /// let key = slab.insert(42);
    /// assert_eq!(Some(&42), slab.get(key));
    /// ```
    pub fn get(&mut self, key: usize) -> Option<&T> {
        self.entries.get(key).and_then(|entry| match entry {
            Entry::Occupied(entry) => Some(entry),
            _ => None,
        })
    }

    /// Get a mutable reference to the value at the given slot.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::pin_slab::PinSlab;
    ///
    /// let mut slab = PinSlab::new();
    /// let key = slab.insert(42);
    /// *slab.get_mut(key).unwrap() = 43;
    /// assert_eq!(Some(&43), slab.get(key));
    /// ```
    pub fn get_mut(&mut self, key: usize) -> Option<&mut T>
    where
        T: Unpin,
    {
        self.entries.get_mut(key).and_then(|entry| match entry {
            Entry::Occupied(entry) => Some(entry),
            _ => None,
        })
    }

    /// Remove the key from the slab.
    ///
    /// Returns `true` if the entry was removed, `false` otherwise.
    /// Removing a key which does not exist has no effect, and `false` will be
    /// returned.
    ///
    /// We need to take care that we don't move it, hence we only perform
    /// operations over pointers below.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::pin_slab::PinSlab;
    ///
    /// let mut slab = PinSlab::new();
    ///
    /// assert!(!slab.remove(0));
    /// let index = slab.insert(42);
    /// assert!(slab.remove(index));
    /// assert!(!slab.remove(index));
    /// ```
    pub fn remove(&mut self, key: usize) -> bool {
        let mut entry = match self.entries.get_pin_mut(key) {
            Some(entry) => entry,
            None => return false,
        };

        match entry.as_mut().project() {
            EntryProject::Occupied(..) => (),
            _ => return false,
        }

        entry.set(Entry::Vacant(self.next));

        self.len -= 1;
        self.next = key;

        true
    }

    /// Clear all available data in the PinSlot.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::pin_slab::PinSlab;
    ///
    /// let mut slab = PinSlab::new();
    /// assert_eq!(0, slab.insert(42));
    /// slab.clear();
    /// assert!(slab.get(0).is_none());
    /// ```
    pub fn clear(&mut self) {
        self.entries.clear()
    }

    /// Insert a value at the given slot.
    fn insert_at(&mut self, key: usize, val: T) {
        if key >= self.entries.len() {
            self.entries
                .extend((self.entries.len()..=key).map(|_| Entry::None));
        }
        let mut entry = self.entries.get_pin_mut(key).unwrap();
        self.next = match entry.as_mut().project() {
            EntryProject::None => key + 1,
            EntryProject::Vacant(next) => *next,
            // NB: unreachable because insert_at is an internal function,
            // which can only be appropriately called on non-occupied
            // entries. This is however, not a safety concern.
            _ => unreachable!(),
        };

        entry.set(Entry::Occupied(val));
        self.len += 1;
    }
}

impl<T> Default for PinSlab<T> {
    fn default() -> Self {
        Self::new()
    }
}
