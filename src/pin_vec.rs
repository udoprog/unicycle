use std::{
    mem::{self, MaybeUninit},
    ops::{Index, IndexMut},
};

pub struct PinVec<T> {
    // Slots of memory. Once one has been allocated it is never moved.
    // This allows us to store entries in there and fetch them as `Pin<&mut T>`.
    slots: Vec<Box<[MaybeUninit<T>]>>,
    // Number of Filled elements currently in the slab
    len: usize,
}

impl<T> PinVec<T> {
    pub fn new() -> Self {
        Self {
            slots: Vec::new(),
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn clear(&mut self) {
        self.slots.clear();
        self.len = 0;
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            let (slot, offset, _) = calculate_key(index);
            // Safety: We guarantee that all indices <= self.len are initialized
            unsafe { Some(self.slots[slot][offset].assume_init_ref()) }
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len() {
            let (slot, offset, _) = calculate_key(index);
            // Safety: We guarantee that all indices <= self.len are initialized
            unsafe { Some(self.slots[slot][offset].assume_init_mut()) }
        } else {
            None
        }
    }

    pub fn push(&mut self, item: T) {
        let (slot, offset, slot_len) = calculate_key(self.len);

        if slot == self.slots.len() {
            self.slots
                .push((0..slot_len).map(|_| MaybeUninit::uninit()).collect());
        }

        self.slots[slot][offset].write(item);

        self.len += 1;
    }

    pub fn extend(&mut self, items: impl Iterator<Item = T>) {
        for item in items {
            self.push(item)
        }
    }
}

impl<T> Index<usize> for PinVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T> IndexMut<usize> for PinVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

// Size of the first slot.
const FIRST_SLOT_SIZE: usize = 16;
// The initial number of bits to ignore for the first slot.
const FIRST_SLOT_MASK: usize =
    std::mem::size_of::<usize>() * 8 - FIRST_SLOT_SIZE.leading_zeros() as usize - 1;

/// Calculate the key as a (slot, offset, len) tuple.
const fn calculate_key(key: usize) -> (usize, usize, usize) {
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

#[cfg(test)]
mod tests {
    use crate::pin_vec::calculate_key;

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
}
