//! A hierarchical bit set with support for atomic operations.
//!
//! The idea is based on [hibitset], but dynamically growing instead of using a
//! fixed capacity.
//! By being careful with the data layout, we can also support structural
//! sharing between the local and atomic bitset variants.
//!
//! [hibitset]: https://docs.rs/hibitset

use std::{
    iter, mem, ops, slice,
    sync::atomic::{AtomicUsize, Ordering},
};

#[cfg(feature = "vec-safety")]
use self::vec_safety::Layers;
#[cfg(not(feature = "vec-safety"))]
type Layers<T> = Vec<T>;

/// A private marker trait that promises that the implementing type has an
/// identical memory layout to a Layer].
///
/// The only purpose of this trait is to server to make convert_layer safer.
///
/// # Safety
///
/// Implementer must assert that the implementing type has an identical layout
/// to a [Layer].
unsafe trait IsLayer {}

/// Bits in a single usize.
const BITS: usize = mem::size_of::<usize>() * 8;
const BITS_SHIFT: usize = BITS.trailing_zeros() as usize;

/// Precalculated shifts for each layer.
///
/// The shift is used to shift the bits in a given index to the least
/// significant position so it can be used as an index for that layer.
static SHIFTS: [usize; 11] = [
    0,
    1 * BITS_SHIFT,
    2 * BITS_SHIFT,
    3 * BITS_SHIFT,
    4 * BITS_SHIFT,
    5 * BITS_SHIFT,
    6 * BITS_SHIFT,
    7 * BITS_SHIFT,
    8 * BITS_SHIFT,
    9 * BITS_SHIFT,
    10 * BITS_SHIFT,
];

/// Precalculated widths of each layer.
static WIDTHS: [usize; 11] = [
    BITS << SHIFTS[0],
    BITS << SHIFTS[1],
    BITS << SHIFTS[2],
    BITS << SHIFTS[3],
    BITS << SHIFTS[4],
    BITS << SHIFTS[5],
    BITS << SHIFTS[6],
    BITS << SHIFTS[7],
    BITS << SHIFTS[8],
    BITS << SHIFTS[9],
    BITS << SHIFTS[10],
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct LayerLayout {
    /// The length of the layer.
    cap: usize,
}

/// A sparse, layered bit set.
///
/// Layered bit sets support exceedingly efficient iteration, union, and
/// intersection operations since they maintain summary layers summarizing the
/// bits which are sets in layers below it.
///
/// [BitSet] and [AtomicBitSet]'s are guaranteed to have an identical memory
/// layout, so while it would require `unsafe`, transmuting or coercing between
/// the two is sound assuming the proper synchronization is respected.
///
/// A [BitSet] provides the following methods for converting to an
/// [AtomicBitSet]: [into_atomic] and [as_atomic].
///
/// [into_atomic]: BitSet::into_atomic
/// [as_atomic]: BitSet::as_atomic
#[repr(C)]
pub struct BitSet {
    /// Layers of bits.
    // TODO: Consider breaking this up into a (pointer, len, cap) tuple since
    // I'm not entirely sure this guarantees that the memory layout of `BitSet`
    // is the same as `AtomicBitSet`, even though `Layer` and `AtomicLayer` is.
    layers: Layers<Layer>,
    /// The capacity of the bitset in number of bits it can store.
    cap: usize,
}

impl BitSet {
    /// Construct a new, empty BitSet with an empty capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::new();
    /// assert!(set.is_empty());
    /// assert_eq!(0, set.capacity());
    /// ```
    pub fn new() -> Self {
        Self {
            layers: Layers::new(),
            cap: 0,
        }
    }

    /// Construct a new, empty [BitSet] with the specified capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(1024);
    /// assert!(set.is_empty());
    /// assert_eq!(1024, set.capacity());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        let mut this = Self::new();
        this.reserve(capacity);
        this
    }

    /// Test if the bit set is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(64);
    /// assert!(set.is_empty());
    /// set.set(2);
    /// assert!(!set.is_empty());
    /// set.clear(2);
    /// assert!(set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        // The top, summary layer is zero.
        self.layers.last().map(|l| l[0] == 0).unwrap_or(true)
    }

    /// Get the current capacity of the bitset.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::new();
    /// assert!(set.is_empty());
    /// assert_eq!(0, set.capacity());
    /// ```
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Return a view of the underlying, raw layers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(128);
    /// set.set(1);
    /// set.set(5);
    /// // Note: two layers since we specified a capacity of 128.
    /// assert_eq!(vec![&[0b100010, 0][..], &[1]], set.layers());
    /// ```
    pub fn layers(&self) -> Vec<&'_ [usize]> {
        self.layers.as_slice().iter().map(Layer::as_slice).collect()
    }

    /// Convert in-place into an [AtomicBitSet].
    ///
    /// Atomic bit sets uses structural sharing with the current set, so this
    /// is a constant time `O(1)` operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(1024);
    ///
    /// let atomic = set.into_atomic();
    /// atomic.set(42);
    ///
    /// let set = atomic.into_local();
    /// assert!(set.test(42));
    /// ```
    pub fn into_atomic(mut self) -> AtomicBitSet {
        AtomicBitSet {
            layers: convert_layers(mem::replace(&mut self.layers, Layers::new())),
            cap: mem::replace(&mut self.cap, 0),
        }
    }

    /// Convert in-place into a reference to an [AtomicBitSet].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let set = BitSet::with_capacity(1024);
    ///
    /// set.as_atomic().set(42);
    /// assert!(set.test(42));
    /// ```
    pub fn as_atomic(&self) -> &AtomicBitSet {
        // Safety: BitSet and AtomicBitSet are guaranteed to have identical
        // memory layouts.
        unsafe { &*(self as *const _ as *const AtomicBitSet) }
    }

    /// Set the given bit.
    ///
    /// # Panics
    ///
    /// Panics if the position does not fit within the capacity of the [BitSet].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(64);
    ///
    /// assert!(set.is_empty());
    /// set.set(2);
    /// assert!(!set.is_empty());
    /// ```
    pub fn set(&mut self, mut position: usize) {
        assert!(
            position < self.cap,
            "position {} is out of bounds for capacity {}",
            position,
            self.cap
        );

        for layer in &mut self.layers {
            let slot = position / BITS;
            let offset = position % BITS;
            layer.set(slot, offset);
            position >>= BITS_SHIFT;
        }
    }

    /// Clear the given bit.
    ///
    /// # Panics
    ///
    /// Panics if the position does not fit within the capacity of the [BitSet].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(64);
    ///
    /// set.clear(2);
    /// assert!(set.is_empty());
    /// set.set(2);
    /// assert!(!set.is_empty());
    /// set.clear(2);
    /// assert!(set.is_empty());
    /// set.clear(2);
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self, mut position: usize) {
        assert!(
            position < self.cap,
            "position {} is out of bounds for capacity {}",
            position,
            self.cap
        );

        for layer in &mut self.layers {
            let slot = position / BITS;
            let offset = position % BITS;
            layer.clear(slot, offset);
            position >>= BITS_SHIFT;
        }
    }

    /// Test if the given position is set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(64);
    ///
    /// assert!(set.is_empty());
    /// set.set(2);
    /// assert!(!set.is_empty());
    /// assert!(set.test(2));
    /// assert!(!set.test(3));
    /// ```
    pub fn test(&self, position: usize) -> bool {
        assert!(position < self.cap);
        let slot = position / BITS;
        let offset = position % BITS;
        self.layers[0].test(slot, offset)
    }

    /// Reserve enough space to store the given number of elements.
    ///
    /// This will not reserve space for exactly as many elements specified, but
    /// will round up to the closest order of magnitude of 2.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    /// let mut set = BitSet::with_capacity(128);
    /// assert_eq!(128, set.capacity());
    /// set.reserve(250);
    /// assert_eq!(256, set.capacity());
    /// ```
    pub fn reserve(&mut self, cap: usize) {
        if self.cap >= cap {
            return;
        }

        let cap = round_capacity_up(cap);
        let mut new = bit_set_layout(cap).peekable();

        let mut old = self.layers.as_mut_slice().iter_mut();

        while let (Some(layer), Some(&LayerLayout { cap, .. })) = (old.next(), new.peek()) {
            debug_assert!(cap >= layer.cap);

            // Layer needs to grow.
            if cap > 0 {
                layer.grow(cap);
            }

            // Skip to next new layer.
            new.next();
        }

        let remaining = new.clone().count();

        // Add new layers!
        if remaining > 0 {
            self.layers.reserve_exact(remaining);
            self.layers.extend(new.map(|l| Layer::with_capacity(l.cap)));
        }

        self.cap = cap;
    }

    /// Create a draining iterator over the bitset, yielding all elements in
    /// order of their index.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(128);
    /// set.set(127);
    /// set.set(32);
    /// set.set(3);
    ///
    /// assert_eq!(vec![3, 32, 127], set.drain().collect::<Vec<_>>());
    /// assert!(set.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<'_> {
        let depth = self.layers.len().saturating_sub(1);

        let layers = if self.is_empty() {
            &mut []
        } else {
            self.layers.as_mut_slice()
        };

        Drain {
            layers,
            index: 0,
            depth,
            #[cfg(test)]
            op_count: 0,
        }
    }

    /// Create an iterator over the bitset, yielding all elements in order of
    /// their index.
    ///
    /// Note that iterator allocates a vector with a size matching the number of
    /// layers in the [BitSet].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(128);
    /// set.set(127);
    /// set.set(32);
    /// set.set(3);
    ///
    /// assert_eq!(vec![3, 32, 127], set.iter().collect::<Vec<_>>());
    /// assert!(!set.is_empty());
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        let depth = self.layers.len().saturating_sub(1);

        Iter {
            layers: self.layers.as_slice(),
            masks: (0..self.layers.len()).map(|_| !0).collect(),
            index: 0,
            depth,
            #[cfg(test)]
            op_count: 0,
        }
    }
}

impl Default for BitSet {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Drain<'a> {
    layers: &'a mut [Layer],
    index: usize,
    depth: usize,
    #[cfg(test)]
    pub(crate) op_count: usize,
}

impl Iterator for Drain<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.layers.is_empty() {
            return None;
        }

        loop {
            #[cfg(test)]
            {
                self.op_count += 1;
            }

            let offset = self.index / WIDTHS[self.depth];
            let slot = &mut self.layers[self.depth][offset];

            // We should never hit a layer which is zeroed.
            debug_assert!(*slot != 0);

            if self.depth > 0 {
                // Advance into a deeper layer. We set the base index to
                // the value of the deeper layer.
                //
                // We calculate the index based on the offset that we are
                // currently at and the information we get at the current
                // layer of bits.
                self.index = (offset * WIDTHS[self.depth])
                    + ((slot.trailing_zeros() as usize) << SHIFTS[self.depth]);
                self.depth -= 1;
                continue;
            }

            // We are now in layer 0. The number of trailing zeros indicates
            // the bit set.
            let trail = slot.trailing_zeros() as usize;

            // NB: if this doesn't hold, a prior layer lied and we ended up
            // here in vain.
            debug_assert!(trail < BITS);

            let index = self.index + trail;

            // NB: assert that we are actually unsetting a bit.
            debug_assert!(*slot & !(1 << trail) != *slot);

            // Clear the current slot.
            *slot &= !(1 << trail);

            // Slot is not empty yet.
            if *slot != 0 {
                return Some(index);
            }

            // Clear upper layers until we find one that is not set again -
            // then use that as hour new depth.
            for (depth, layer) in (1..).zip(self.layers[1..].iter_mut()) {
                #[cfg(test)]
                {
                    self.op_count += 1;
                }

                let offset = self.index / WIDTHS[depth];
                let slot = &mut layer[offset];

                // If this doesn't hold, then we have previously failed at
                // populating the summary layers of the set.
                debug_assert!(*slot != 0);

                *slot &= !(1 << ((index >> SHIFTS[depth]) % BITS));

                if *slot != 0 {
                    // update the index to be the bottom of the next value set
                    // layer.
                    self.depth = depth;

                    // We calculate the index based on the offset that we are
                    // currently at and the information we get at the current
                    // layer of bits.
                    self.index = (offset * WIDTHS[depth])
                        + ((slot.trailing_zeros() as usize) << SHIFTS[depth]);
                    return Some(index);
                }
            }

            // The entire bitset is cleared. We are done.
            self.layers = &mut [];
            return Some(index);
        }
    }
}

pub struct Iter<'a> {
    layers: &'a [Layer],
    masks: Vec<usize>,
    index: usize,
    depth: usize,
    #[cfg(test)]
    pub(crate) op_count: usize,
}

impl Iterator for Iter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.layers.is_empty() {
            return None;
        }

        loop {
            #[cfg(test)]
            {
                self.op_count += 1;
            }

            let mask = &mut self.masks[self.depth];
            let offset = self.index / WIDTHS[self.depth];
            let slot = self.layers[self.depth][offset] & *mask;

            if slot == 0 {
                *mask = !0;
                self.depth += 1;

                if self.depth == self.layers.len() {
                    self.layers = &[];
                    return None;
                }
            } else {
                let tail = slot.trailing_zeros() as usize;

                if tail == BITS - 1 {
                    *mask = 0;
                } else {
                    *mask = !0 << (tail + 1);
                }

                // Advance one layer down, setting the index to the bit matching
                // the offset we are interested in.
                if self.depth > 0 {
                    self.index = (offset * WIDTHS[self.depth]) + (tail << SHIFTS[self.depth]);
                    self.depth -= 1;
                    continue;
                }

                return Some(self.index + tail);
            }
        }
    }
}

/// The same as [BitSet], except it provides atomic methods.
///
/// [BitSet] and [AtomicBitSet]'s are guaranteed to have an identical memory
/// layout, so while it would require `unsafe`, transmuting or coercing between
/// the two is sound assuming the proper synchronization is respected.
///
/// We provide the following methods to accomplish this from an atomic bitset,
/// to a local (non atomic) one: [as_local_mut] for borrowing mutably and
/// [into_local].
///
/// [as_local_mut]: AtomicBitSet::as_local_mut
/// [into_local]: AtomicBitSet::into_local
#[repr(C)]
pub struct AtomicBitSet {
    /// Layers of bits.
    layers: Layers<AtomicLayer>,
    /// The capacity of the bit set in number of bits it can store.
    cap: usize,
}

impl AtomicBitSet {
    /// Construct a new, empty atomic bit set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::AtomicBitSet;
    ///
    /// let set = AtomicBitSet::new();
    /// let set = set.into_local();
    /// assert!(set.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            layers: Layers::new(),
            cap: 0,
        }
    }

    /// Set the given bit atomically.
    ///
    /// We can do this to an [AtomicBitSet] since the required modifications
    /// that needs to be performed against each layer are idempotent of the
    /// order in which they are applied.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let set = BitSet::with_capacity(1024).into_atomic();
    /// set.set(1000);
    /// let set = set.into_local();
    /// assert!(set.test(1000));
    /// ```
    pub fn set(&self, mut position: usize) {
        assert!(
            position < self.cap,
            "position {} is out of bounds for layer capacity {}",
            position,
            self.cap
        );

        for layer in &self.layers {
            let slot = position / BITS;
            let offset = position % BITS;
            layer.set(slot, offset);
            position >>= BITS_SHIFT;
        }
    }

    /// Convert in-place into a a [`BitSet`].
    ///
    /// This is safe, since this function requires exclusive owned access to the
    /// [AtomicBitSet], and we assert that their memory layouts are identical.
    ///
    /// [`BitSet`]: BitSet
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::new();
    /// set.reserve(1024);
    ///
    /// let atomic = set.into_atomic();
    /// atomic.set(42);
    ///
    /// let set = atomic.into_local();
    /// assert!(set.test(42));
    /// ```
    pub fn into_local(mut self) -> BitSet {
        BitSet {
            layers: convert_layers(mem::replace(&mut self.layers, Layers::new())),
            cap: mem::replace(&mut self.cap, 0),
        }
    }

    /// Convert in-place into a mutable reference to a [`BitSet`].
    ///
    /// This is safe, since this function requires exclusive mutable access to
    /// the [AtomicBitSet], and we assert that their memory layouts are
    /// identical.
    ///
    /// [`BitSet`]: BitSet
    ///
    /// # Examples
    ///
    /// ```rust
    /// use unicycle::BitSet;
    ///
    /// let mut set = BitSet::with_capacity(1024).into_atomic();
    ///
    /// set.set(21);
    /// set.set(42);
    ///
    /// {
    ///     let set = set.as_local_mut();
    ///     // Clearing is only safe with BitSet's since we require exclusive
    ///     // mutable access to the collection being cleared.
    ///     set.clear(21);
    /// }
    ///
    /// let set = set.into_local();
    /// assert!(!set.test(21));
    /// assert!(set.test(42));
    /// ```
    pub fn as_local_mut(&mut self) -> &mut BitSet {
        // Safety: BitSet and AtomicBitSet are guaranteed to have identical
        // internal structures.
        unsafe { &mut *(self as *mut _ as *mut BitSet) }
    }
}

impl Default for AtomicBitSet {
    fn default() -> Self {
        Self::new()
    }
}

/// A single layer of bits.
///
/// Note: doesn't store capacity, so must be deallocated by a BitSet.
#[repr(C)]
struct Layer {
    /// Bits.
    bits: *mut usize,
    cap: usize,
}

unsafe impl IsLayer for Layer {}
unsafe impl Send for Layer {}
unsafe impl Sync for Layer {}

impl Layer {
    /// Allocate a new raw layer with the specified capacity.
    pub fn with_capacity(cap: usize) -> Layer {
        // Create an already initialized layer of bits.
        let mut vec = mem::ManuallyDrop::new(vec![0usize; cap]);

        Layer {
            bits: vec.as_mut_ptr(),
            cap,
        }
    }

    /// Return the given layer as a slice.
    pub fn as_slice(&self) -> &[usize] {
        unsafe { slice::from_raw_parts(self.bits, self.cap) }
    }

    /// Return the given layer as a mutable slice.
    pub fn as_mut_slice(&mut self) -> &mut [usize] {
        unsafe { slice::from_raw_parts_mut(self.bits, self.cap) }
    }

    /// Reserve exactly the specified number of elements in this layer.
    pub fn grow(&mut self, new: usize) {
        // Nothing to do.
        if self.cap >= new {
            return;
        }

        let mut vec =
            mem::ManuallyDrop::new(unsafe { Vec::from_raw_parts(self.bits, self.cap, self.cap) });
        vec.reserve(new - self.cap);

        // Initialize new values.
        for _ in self.cap..new {
            vec.push(0usize);
        }

        debug_assert!(vec.len() == vec.capacity());
        self.bits = vec.as_mut_ptr();
        self.cap = vec.capacity();
    }

    /// Set the given bit in this layer.
    pub fn set(&mut self, slot: usize, offset: usize) {
        *self.slot_mut(slot) |= 1 << offset;
    }

    /// Clear the given bit in this layer.
    pub fn clear(&mut self, slot: usize, offset: usize) {
        *self.slot_mut(slot) &= !(1 << offset);
    }

    /// Set the given bit in this layer, where `element` indicates how many
    /// elements are affected per position.
    pub fn test(&self, slot: usize, offset: usize) -> bool {
        *self.slot(slot) & (1 << offset) > 0
    }

    #[inline(always)]
    fn slot(&self, slot: usize) -> &usize {
        assert!(slot < self.cap);
        // Safety: We check that the slot fits within the capacity.
        unsafe { &*self.bits.add(slot) }
    }

    #[inline(always)]
    fn slot_mut(&mut self, slot: usize) -> &mut usize {
        assert!(slot < self.cap);
        // Safety: We check that the slot fits within the capacity.
        unsafe { &mut *self.bits.add(slot) }
    }
}

impl<S> PartialEq<S> for Layer
where
    S: AsRef<[usize]>,
{
    fn eq(&self, other: &S) -> bool {
        other.as_ref() == self.as_slice()
    }
}

impl Eq for Layer {}

impl AsRef<[usize]> for Layer {
    fn as_ref(&self) -> &[usize] {
        self.as_slice()
    }
}

impl<I: slice::SliceIndex<[usize]>> ops::Index<I> for Layer {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::index(self.as_slice(), index)
    }
}

impl<I: slice::SliceIndex<[usize]>> ops::IndexMut<I> for Layer {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        ops::IndexMut::index_mut(self.as_mut_slice(), index)
    }
}

impl Drop for Layer {
    fn drop(&mut self) {
        unsafe {
            drop(Vec::from_raw_parts(self.bits, self.cap, self.cap));
        }
    }
}

/// A single layer of the bitset, that can be atomically updated.
///
/// Note: This has the same memory layout as [Layer], so that coercing between
/// them is possible.
#[repr(C)]
struct AtomicLayer {
    bits: *mut AtomicUsize,
    cap: usize,
}

unsafe impl IsLayer for AtomicLayer {}
unsafe impl Send for AtomicLayer {}
unsafe impl Sync for AtomicLayer {}

impl AtomicLayer {
    /// Return the given layer as a slice.
    pub fn as_slice(&self) -> &[AtomicUsize] {
        unsafe { slice::from_raw_parts(self.bits, self.cap) }
    }

    /// Set the given bit in this layer, where `element` indicates how many
    /// elements are affected per position.
    pub fn set(&self, slot: usize, offset: usize) {
        // Ordering: We rely on external synchronization when testing the layers
        // So total memory ordering does not matter as long as we apply all
        // necessary operations to all layers - which is guaranteed by
        // [AtomicBitSet::set].
        self.slot(slot).fetch_or(1 << offset, Ordering::Relaxed);
    }

    #[inline(always)]
    fn slot(&self, slot: usize) -> &AtomicUsize {
        assert!(slot < self.cap);
        // Safety: We check that the slot fits within the capacity.
        unsafe { &*self.bits.add(slot) }
    }
}

impl AsRef<[AtomicUsize]> for AtomicLayer {
    fn as_ref(&self) -> &[AtomicUsize] {
        self.as_slice()
    }
}

impl Drop for AtomicLayer {
    fn drop(&mut self) {
        // Safety: We keep track of the capacity internally.
        unsafe {
            drop(Vec::from_raw_parts(self.bits, self.cap, self.cap));
        }
    }
}

fn round_bits_up(value: usize) -> usize {
    let m = value % BITS;

    if m == 0 {
        value
    } else {
        value + (BITS - m)
    }
}

/// Helper function to generate the necessary layout of the bit set layers
/// given a desired `capacity`.
fn bit_set_layout(capacity: usize) -> impl Iterator<Item = LayerLayout> + Clone {
    let mut cap = round_bits_up(capacity);

    iter::from_fn(move || {
        if cap == 1 {
            return None;
        }

        cap = round_bits_up(cap) / BITS;

        if cap > 0 {
            Some(LayerLayout { cap })
        } else {
            None
        }
    })
}

/// Round up the capacity to be the closest power of 2.
fn round_capacity_up(cap: usize) -> usize {
    if cap == 0 {
        return 0;
    }

    let cap = if BITS as u32 - cap.leading_zeros() == cap.trailing_zeros() + 1 {
        cap
    } else {
        let leading = cap.leading_zeros();

        if leading == 64 {
            return std::usize::MAX;
        }

        1 << (64 - cap.leading_zeros() as usize)
    };

    usize::max(16, cap)
}

/// Convert a vector into a different type, assuming the constituent type has
/// an identical layout to the converted type.
fn convert_layers<T, U>(vec: Layers<T>) -> Layers<U>
where
    T: IsLayer,
    U: IsLayer,
{
    debug_assert!(mem::size_of::<T>() == mem::size_of::<U>());
    debug_assert!(mem::align_of::<T>() == mem::align_of::<U>());

    let mut vec = mem::ManuallyDrop::new(vec);

    // Safety: we guarantee safety by requiring that `T` and `U` implements
    // `IsLayer`.
    unsafe { Layers::from_raw_parts(vec.as_mut_ptr() as *mut U, vec.len(), vec.capacity()) }
}

#[cfg(feature = "vec-safety")]
mod vec_safety {
    use std::{iter, marker, mem, ops, slice};

    /// Storage for layers.
    ///
    /// We use this _instead_ of `Vec<T>` since we want layout guarantees.
    ///
    /// Note: this type is underdocumented since it is internal, and its only
    /// goal is to provide an equivalent compatible API as Vec<T>, so look
    /// there for documentation.
    #[repr(C)]
    pub struct Layers<T> {
        data: *const T,
        len: usize,
        cap: usize,
        _marker: marker::PhantomData<T>,
    }

    unsafe impl<T> Send for Layers<T> where T: Send {}
    unsafe impl<T> Sync for Layers<T> where T: Sync {}

    impl<T> Layers<T> {
        /// Note: Can't be a constant function :(.
        pub fn new() -> Self {
            let vec = mem::ManuallyDrop::new(Vec::<T>::new());

            Self {
                data: vec.as_ptr(),
                len: vec.len(),
                cap: vec.capacity(),
                _marker: marker::PhantomData,
            }
        }

        pub fn reserve_exact(&mut self, cap: usize) {
            self.as_vec(|vec| vec.reserve_exact(cap));
        }

        pub fn as_mut_ptr(&mut self) -> *mut T {
            self.data as *mut T
        }

        pub fn len(&self) -> usize {
            self.len
        }

        pub fn is_empty(&self) -> bool {
            self.len == 0
        }

        pub fn capacity(&self) -> usize {
            self.cap
        }

        pub fn as_mut_slice(&mut self) -> &mut [T] {
            unsafe { slice::from_raw_parts_mut(self.data as *mut T, self.len) }
        }

        pub fn as_slice(&self) -> &[T] {
            unsafe { slice::from_raw_parts(self.data, self.len) }
        }

        pub fn last(&self) -> Option<&T> {
            self.as_slice().last()
        }

        pub unsafe fn from_raw_parts(data: *mut T, len: usize, cap: usize) -> Self {
            Self {
                data,
                len,
                cap,
                _marker: marker::PhantomData,
            }
        }

        #[inline(always)]
        fn as_vec<F>(&mut self, f: F)
        where
            F: FnOnce(&mut Vec<T>),
        {
            let mut vec = mem::ManuallyDrop::new(unsafe {
                Vec::from_raw_parts(self.data as *mut T, self.len, self.cap)
            });
            f(&mut vec);
            self.data = vec.as_mut_ptr();
            self.len = vec.len();
            self.cap = vec.capacity();
        }
    }

    impl<'a, T> IntoIterator for &'a mut Layers<T> {
        type IntoIter = slice::IterMut<'a, T>;
        type Item = &'a mut T;

        fn into_iter(self) -> Self::IntoIter {
            self.as_mut_slice().into_iter()
        }
    }

    impl<'a, T> IntoIterator for &'a Layers<T> {
        type IntoIter = slice::Iter<'a, T>;
        type Item = &'a T;

        fn into_iter(self) -> Self::IntoIter {
            self.as_slice().into_iter()
        }
    }

    impl<T, I: slice::SliceIndex<[T]>> ops::Index<I> for Layers<T> {
        type Output = I::Output;

        #[inline]
        fn index(&self, index: I) -> &Self::Output {
            ops::Index::index(self.as_slice(), index)
        }
    }

    impl<T, I: slice::SliceIndex<[T]>> ops::IndexMut<I> for Layers<T> {
        #[inline]
        fn index_mut(&mut self, index: I) -> &mut Self::Output {
            ops::IndexMut::index_mut(self.as_mut_slice(), index)
        }
    }

    impl<T> iter::Extend<T> for Layers<T> {
        #[inline]
        fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
            self.as_vec(|vec| vec.extend(iter));
        }
    }

    impl<T> Drop for Layers<T> {
        fn drop(&mut self) {
            drop(unsafe { Vec::from_raw_parts(self.data as *mut T, self.len, self.cap) });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{bit_set_layout, AtomicBitSet, BitSet};

    #[test]
    fn assert_send_and_sync() {
        assert_traits(BitSet::new());
        assert_traits(AtomicBitSet::new());

        fn assert_traits<T: Send + Sync>(_: T) {}
    }

    #[test]
    fn test_set_and_test() {
        let mut set = BitSet::new();
        set.reserve(1024);
        set.set(1);
        set.set(64);
        set.set(129);
        set.set(1023);

        assert!(set.test(1));
        assert!(set.test(64));
        assert!(set.test(129));
        assert!(set.test(1023));
        assert!(!set.test(1022));

        let mut layer0 = vec![0usize; 16];
        layer0[0] = 1 << 1;
        layer0[1] = 1;
        layer0[2] = 1 << 1;
        layer0[15] = 1 << 63;

        let mut layer1 = vec![0usize; 1];
        layer1[0] = 1 << 15 | 1 << 2 | 1 << 1 | 1;

        assert_eq!(vec![&layer0[..], &layer1[..]], set.layers());
    }

    #[test]
    fn test_bit_layout() {
        assert!(bit_set_layout(0).collect::<Vec<_>>().is_empty());
        assert_eq!(
            vec![1],
            bit_set_layout(64).map(|l| l.cap).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![2, 1],
            bit_set_layout(128).map(|l| l.cap).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![64, 1],
            bit_set_layout(4096).map(|l| l.cap).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![65, 2, 1],
            bit_set_layout(4097).map(|l| l.cap).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![2, 1],
            bit_set_layout(65).map(|l| l.cap).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![2, 1],
            bit_set_layout(128).map(|l| l.cap).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![3, 1],
            bit_set_layout(129).map(|l| l.cap).collect::<Vec<_>>()
        );
        assert_eq!(
            vec![65, 2, 1],
            bit_set_layout(4097).map(|l| l.cap).collect::<Vec<_>>()
        );
    }

    // NB: test to run through miri to make sure we reserve layers appropriately.
    #[test]
    fn test_reserve() {
        let mut b = BitSet::new();
        b.reserve(1_000);
        b.reserve(10_000);

        assert_ne!(
            bit_set_layout(1_000).collect::<Vec<_>>(),
            bit_set_layout(10_000).collect::<Vec<_>>()
        );
    }

    macro_rules! drain_test {
        ($cap:expr, $sample:expr, $expected_op_count:expr) => {{
            let mut set = BitSet::new();
            set.reserve($cap);

            let positions: Vec<usize> = $sample;

            for p in positions.iter().copied() {
                set.set(p);
            }

            let mut drain = set.drain();
            assert_eq!(positions, (&mut drain).collect::<Vec<_>>());
            let op_count = drain.op_count;

            // Assert that all layers are zero.
            assert!(set.layers().into_iter().all(|l| l.iter().all(|n| *n == 0)));

            assert_eq!($expected_op_count, op_count);
        }};
    }

    macro_rules! iter_test {
        ($cap:expr, $sample:expr, $expected_op_count:expr) => {{
            let mut set = BitSet::new();
            set.reserve($cap);

            let positions: Vec<usize> = $sample;

            for p in positions.iter().copied() {
                set.set(p);
            }

            let mut iter = set.iter();
            assert_eq!(positions, (&mut iter).collect::<Vec<_>>());
            let op_count = iter.op_count;

            assert_eq!($expected_op_count, op_count);
        }};
    }

    #[test]
    fn test_drain() {
        drain_test!(0, vec![], 0);
        drain_test!(1024, vec![], 0);
        drain_test!(64, vec![0], 1);
        drain_test!(64, vec![0, 1], 2);
        drain_test!(64, vec![0, 1, 63], 3);
        drain_test!(128, vec![64], 3);
        drain_test!(128, vec![0, 32, 64], 7);
        drain_test!(4096, vec![0, 32, 64, 3030, 4095], 13);
        drain_test!(
            1_000_000,
            vec![0, 32, 64, 3030, 4095, 50_000, 102110, 203020, 500000, 803020, 900900],
            51
        );
        drain_test!(
            10_000_000,
            vec![0, 32, 64, 3030, 4095, 50_000, 102110, 203020, 500000, 803020, 900900, 9_009_009],
            58
        );
    }

    #[test]
    fn test_iter() {
        iter_test!(0, vec![], 0);
        iter_test!(1024, vec![], 1);
        iter_test!(64, vec![0, 2], 3);
        iter_test!(64, vec![0, 1], 3);
        iter_test!(128, vec![64], 4);
        iter_test!(128, vec![0, 32, 64], 8);
        iter_test!(4096, vec![0, 32, 64, 3030, 4095], 14);
        iter_test!(
            1_000_000,
            vec![0, 32, 64, 3030, 4095, 50_000, 102110, 203020, 500000, 803020, 900900],
            52
        );
        iter_test!(
            10_000_000,
            vec![0, 32, 64, 3030, 4095, 50_000, 102110, 203020, 500000, 803020, 900900, 9_009_009],
            59
        );
    }

    #[test]
    fn test_round_capacity_up() {
        use super::round_capacity_up;
        assert_eq!(0, round_capacity_up(0));
        assert_eq!(16, round_capacity_up(1));
        assert_eq!(32, round_capacity_up(17));
        assert_eq!(32, round_capacity_up(32));
        assert_eq!(
            (std::usize::MAX >> 1) + 1,
            round_capacity_up(std::usize::MAX >> 1)
        );
    }
}
