//! A slab-like, pre-allocated storage where the slab is divided into immovable
//! slots. Each allocated slot doubles the capacity of the slab.
//!
//! Converted from <https://github.com/carllerche/slab>, this slab however
//! contains a growable collection of fixed-size regions called slots.
//! This allows is to store immovable objects inside the slab, since growing the
//! collection doesn't require the existing slots to move.

use std::{mem, pin::Pin, ptr};

// Size of the first slot.
const FIRST_SLOT_SIZE: usize = 16;
// The initial number of bits to ignore for the first slot.
const FIRST_SLOT_MASK: usize =
    std::mem::size_of::<usize>() * 8 - FIRST_SLOT_SIZE.leading_zeros() as usize - 1;

/// Pre-allocated storage for a uniform data type.
#[derive(Clone)]
pub(crate) struct PinSlab<T> {
    // Slots of memory. Once one has been allocated it is never moved.
    // This allows us to store entries in there and fetch them as `Pin<&mut T>`.
    slots: Vec<ptr::NonNull<Entry<T>>>,
    // Number of Filled elements currently in the slab
    len: usize,
    // Offset of the next available slot in the slab.
    next: usize,
}

unsafe impl<T> Send for PinSlab<T> {}
unsafe impl<T> Sync for PinSlab<T> {}

enum Entry<T> {
    // Each slot is pre-allocated with entries of `None`.
    None,
    // Removed entries are replaced with the vacant tomb stone, pointing to the
    // next vacant entry.
    Vacant(usize),
    // An entry that is occupied with a value.
    Occupied(T),
}

impl<T> PinSlab<T> {
    /// Construct a new, empty [PinSlab] with the default slot size.
    pub fn new() -> Self {
        Self {
            slots: Vec::new(),
            next: 0,
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    /// Test if the pin slab is empty.
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
        let (slot, offset, len) = calculate_key(key);
        let slot = *self.slots.get_mut(slot)?;

        // Safety: all slots are fully allocated and initialized in `new_slot`.
        // As long as we have access to it, we know that we will only find
        // initialized entries assuming offset < len.
        debug_assert!(offset < len);
        let entry = match unsafe { &mut *slot.as_ptr().add(offset) } {
            Entry::Occupied(entry) => entry,
            _ => return None,
        };

        // Safety: all storage is pre-allocated in chunks, and each chunk
        // doesn't move. We only provide mutators to drop the storage through
        // `remove` (but it doesn't return it).
        Some(unsafe { Pin::new_unchecked(entry) })
    }

    /// Remove the key from the slab.
    ///
    /// Returns `true` if the entry was removed, `false` otherwise.
    /// Removing a key which does not exist have no effect.
    ///
    /// We need to take care that we don't move it, hence we only perform
    /// operations over pointers below.
    pub fn remove(&mut self, key: usize) -> bool {
        let (slot, offset, len) = calculate_key(key);

        let slot = match self.slots.get_mut(slot) {
            Some(slot) => *slot,
            None => return false,
        };

        // Safety: all slots are fully allocated and initialized in `new_slot`.
        // As long as we have access to it, we know that we will only find
        // initialized entries assuming offset < len.
        debug_assert!(offset < len);
        unsafe {
            let entry = slot.as_ptr().add(offset);

            match &*entry {
                Entry::Occupied(..) => (),
                _ => return false,
            }

            ptr::drop_in_place(entry);
            ptr::write(entry, Entry::Vacant(self.next));
            self.len -= 1;
            self.next = key;
        }

        true
    }

    /// Construct a new slot.
    fn new_slot(&self, len: usize) -> ptr::NonNull<Entry<T>> {
        let mut d = Vec::with_capacity(len);

        for _ in 0..len {
            d.push(Entry::None);
        }

        let ptr = d.as_mut_ptr();
        mem::forget(d);

        // Safety: We just initialized the pointer to be non-null above.
        unsafe { ptr::NonNull::new_unchecked(ptr) }
    }

    /// Insert a value at the given slot.
    fn insert_at(&mut self, key: usize, val: T) {
        let (slot, offset, len) = calculate_key(key);

        if let Some(slot) = self.slots.get_mut(slot) {
            // Safety: all slots are fully allocated and initialized in
            // `new_slot`. As long as we have access to it, we know that we will
            // only find initialized entries assuming offset < slot_size.
            // We also know it's safe to have unique access to _any_ slots,
            // since we have unique access to the slab in this function.
            debug_assert!(offset < len);
            let entry = unsafe { &mut *slot.as_ptr().add(offset) };

            self.next = match *entry {
                Entry::None => key + 1,
                Entry::Vacant(next) => next,
                // NB: unreachable because insert_at is an internal function,
                // which can only be appropriately called on non-occupied
                // entries. This is however, not a safety concern.
                _ => unreachable!(),
            };

            *entry = Entry::Occupied(val);
        } else {
            unsafe {
                let slot = self.new_slot(len);
                *slot.as_ptr() = Entry::Occupied(val);
                self.slots.push(slot);
                self.next = key + 1;
            }
        }

        self.len += 1;
    }
}

impl<T> Drop for PinSlab<T> {
    fn drop(&mut self) {
        // Iterate over all slots and reconstruct each vector - then deallocate
        // it.

        for (len, entry) in slot_sizes().zip(self.slots.iter_mut()) {
            // reconstruct the vector for the slot.
            drop(unsafe { Vec::from_raw_parts(entry.as_ptr(), len, len) });
        }
    }
}

/// Calculate the key as a (slot, offset, len) tuple.
fn calculate_key(key: usize) -> (usize, usize, usize) {
    assert!(key < (1usize << (mem::size_of::<usize>() * 8 - 1)));

    let slot = ((mem::size_of::<usize>() * 8) as usize - key.leading_zeros() as usize)
        .saturating_sub(FIRST_SLOT_MASK);

    let (start, end) = if key < FIRST_SLOT_SIZE {
        (0, FIRST_SLOT_SIZE)
    } else {
        (FIRST_SLOT_SIZE << (slot - 1), FIRST_SLOT_SIZE << slot)
    };

    (slot, key - start, end - start)
}

fn slot_sizes() -> impl Iterator<Item = usize> {
    (0usize..).map(|n| match n {
        0 | 1 => FIRST_SLOT_SIZE,
        n => FIRST_SLOT_SIZE << (n - 1),
    })
}

#[cfg(test)]
mod tests {
    use super::{calculate_key, slot_sizes, PinSlab, FIRST_SLOT_SIZE};

    #[global_allocator]
    static ALLOCATOR: checkers::Allocator = checkers::Allocator::system();

    #[test]
    fn test_slot_sizes() {
        assert_eq!(
            vec![
                FIRST_SLOT_SIZE,
                FIRST_SLOT_SIZE,
                FIRST_SLOT_SIZE << 1,
                FIRST_SLOT_SIZE << 2,
                FIRST_SLOT_SIZE << 3
            ],
            slot_sizes().take(5).collect::<Vec<_>>()
        );
    }

    #[test]
    fn key_test() {
        // NB: range of the first slot.
        assert_eq!((0, 0, 16), calculate_key(0));
        assert_eq!((0, 15, 16), calculate_key(15));

        for i in 4..=62 {
            let end_range = 1usize << i;
            assert_eq!((i - 3, 0, end_range), calculate_key(end_range));
            assert_eq!(
                (i - 3, end_range - 1, end_range),
                calculate_key((1usize << (i + 1)) - 1)
            );
        }
    }

    #[checkers::test]
    fn insert_get_remove_many() {
        let mut slab = PinSlab::new();

        let mut keys = Vec::new();

        for i in 0..1024 {
            keys.push((i as u128, slab.insert(Box::new(i as u128))));
        }

        for (expected, key) in keys.iter().copied() {
            let value = slab.get_pin_mut(key).expect("value to exist");
            assert_eq!(expected, **value.as_ref());
            assert!(slab.remove(key));
        }

        for (_, key) in keys.iter().copied() {
            assert!(slab.get_pin_mut(key).is_none());
        }
    }
}
