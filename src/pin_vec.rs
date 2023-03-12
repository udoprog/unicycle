//! A segmented vector type which pins the element `T`.

#![allow(clippy::len_without_is_empty)]

use std::mem::{self, MaybeUninit};
use std::ops::{Index, IndexMut};
use std::pin::Pin;
use std::ptr::drop_in_place;
use std::slice;

/// A segmented vector type which pins the element `T`.
pub struct PinVec<T> {
    // Slots of memory. Once one has been allocated it is never moved. This
    // allows us to store entries in there and fetch them as `Pin<&mut T>`.
    slots: Vec<Box<[MaybeUninit<T>]>>,
    // Number of initialized elements in the segmented vector. Allows us to calculate
    // how many elements in each slot are initialized.
    len: usize,
}

impl<T> PinVec<T> {
    /// Construct a new empty vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use unicycle::pin_vec::PinVec;
    ///
    /// const VECTOR: PinVec<u32> = PinVec::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            slots: Vec::new(),
            len: 0,
        }
    }

    /// Get the length of the segmented vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use unicycle::pin_vec::PinVec;
    ///
    /// let mut vector = PinVec::<u32>::new();
    ///
    /// assert_eq!(vector.len(), 0);
    /// vector.push(42);
    /// assert_eq!(vector.len(), 1);
    /// vector.clear();
    /// assert_eq!(vector.len(), 0);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Clear the segmented vector, dropping each element in it as appropriate.
    ///
    /// # Examples
    ///
    /// ```
    /// use unicycle::pin_vec::PinVec;
    ///
    /// let mut vector = PinVec::<u32>::new();
    /// vector.push(42);
    /// assert_eq!(vector.get(0), Some(&42));
    /// vector.clear();
    /// assert_eq!(vector.get(0), None);
    /// ```
    pub fn clear(&mut self) {
        if mem::needs_drop::<T>() {
            let (last_slot, offset, _) = calculate_key(self.len());

            for (i, mut slot) in self.slots.drain(..).enumerate() {
                // SAFETY:
                // * We initialized slice to only point to the
                //   already-initialized elements.
                // * It's safe to `drop_in_place` because we are draining the
                //   Vec and have ownership of the elements in the slot.
                unsafe {
                    let len = if i < last_slot { slot.len() } else { offset };
                    let base = slot.as_mut_ptr().cast::<T>();
                    drop_in_place(slice::from_raw_parts_mut(base, len));
                }
            }
        } else {
            self.slots.clear();
        }

        debug_assert_eq!(self.slots.len(), 0);
        self.len = 0;
    }

    /// Get an immutable element from the segmented vector through the given `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unicycle::pin_vec::PinVec;
    ///
    /// let mut vector = PinVec::<u32>::new();
    /// vector.push(42);
    /// assert_eq!(vector.get(0), Some(&42));
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            let (slot, offset, _) = calculate_key(index);
            // Safety: We guarantee that all indices <= self.len are initialized
            unsafe { Some(self.slots[slot][offset].assume_init_ref()) }
        } else {
            None
        }
    }

    /// Get a mutable element from the segmented vector through the given `index` if `T`
    /// is [Unpin].
    ///
    /// # Examples
    ///
    /// ```
    /// use unicycle::pin_vec::PinVec;
    ///
    /// let mut vector = PinVec::<u32>::new();
    /// vector.push(42);
    /// *vector.get_mut(0).unwrap() = 42;
    ///
    /// assert_eq!(vector.get_mut(0), Some(&mut 42));
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T>
    where
        T: Unpin,
    {
        Some(self.get_pin_mut(index)?.get_mut())
    }

    /// Get a pinned element from the segmented vector through the given `index`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::pin::Pin;
    ///
    /// use unicycle::pin_vec::PinVec;
    ///
    /// let mut vector = PinVec::new();
    /// vector.push(async {});
    /// let future: Pin<_> = vector.get_pin_mut(0).unwrap();
    ///
    /// assert!(vector.get_pin_mut(42).is_none());
    /// ```
    pub fn get_pin_mut(&mut self, index: usize) -> Option<Pin<&mut T>> {
        if index < self.len() {
            let (slot, offset, _) = calculate_key(index);

            // SAFETY:
            // * pin: We are fetching an element from a Box<[T]> which this type
            //   guarantees will never move.
            // * uninit: We've checked the length above and know that we are
            //   withing the range of initialized elements.
            unsafe {
                Some(Pin::new_unchecked(
                    self.slots[slot][offset].assume_init_mut(),
                ))
            }
        } else {
            None
        }
    }

    /// Push an element into the segmented vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::pin::Pin;
    ///
    /// use unicycle::pin_vec::PinVec;
    ///
    /// let mut vector = PinVec::new();
    /// vector.push(async {});
    /// let future: Pin<_> = vector.get_pin_mut(0).unwrap();
    ///
    /// assert!(vector.get_pin_mut(42).is_none());
    /// ```
    pub fn push(&mut self, item: T) {
        let (slot, offset, slot_len) = calculate_key(self.len);

        if slot == self.slots.len() {
            let slot = (0..slot_len)
                .map(|_| MaybeUninit::uninit())
                .collect::<Box<[_]>>();
            self.slots.push(slot);
        }

        self.slots[slot][offset].write(item);
        self.len += 1;
    }
}

impl<T> Extend<T> for PinVec<T> {
    #[inline]
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for item in iter {
            self.push(item);
        }
    }
}

impl<T> Drop for PinVec<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T> Index<usize> for PinVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T: Unpin> IndexMut<usize> for PinVec<T> {
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

    let slot = ((mem::size_of::<usize>() * 8) - key.leading_zeros() as usize)
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

    use super::PinVec;

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

    #[test]
    fn run_destructors() {
        let mut destructor_ran = false;

        struct RunDestructor<'a>(&'a mut bool);
        impl<'a> Drop for RunDestructor<'a> {
            fn drop(&mut self) {
                *self.0 = true;
            }
        }

        {
            // Make sure PinVec runs the destructors
            let mut v = PinVec::new();
            v.push(RunDestructor(&mut destructor_ran));
        }

        assert!(destructor_ran);
    }
}
