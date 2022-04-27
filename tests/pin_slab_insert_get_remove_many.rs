use unicycle::pin_slab::PinSlab;

#[global_allocator]
static ALLOCATOR: checkers::Allocator = checkers::Allocator::system();

#[cfg(not(miri))]
const AMOUNT: usize = 1024;
#[cfg(miri)]
const AMOUNT: usize = 128;

#[checkers::test]
fn pin_slab_insert_get_remove_many() {
    let mut slab = PinSlab::new();

    let mut keys = Vec::new();

    for i in 0..AMOUNT {
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
