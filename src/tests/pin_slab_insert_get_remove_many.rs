use crate::task::Storage;

#[cfg(not(miri))]
const AMOUNT: usize = 1024;
#[cfg(miri)]
const AMOUNT: usize = 128;

#[test]
fn pin_slab_insert_get_remove_many() {
    let mut slab = Storage::new();

    let mut keys = Vec::new();

    for i in 0..AMOUNT {
        keys.push((i as u128, slab.insert(Box::new(i as u128))));
    }

    for (expected, key) in keys.iter().copied() {
        let (_, value) = slab.get_pin_mut(key).expect("value to exist");
        assert_eq!(expected, **value.as_ref());
        assert!(slab.remove(key));
    }

    for (_, key) in keys.iter().copied() {
        assert!(slab.get_pin_mut(key).is_none());
    }
}
