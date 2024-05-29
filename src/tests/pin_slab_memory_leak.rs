#![allow(dead_code)]

use crate::task::Storage;

struct Foo(u32);

struct Bar(Vec<u32>);

#[test]
fn test_pin_slab_memory_leak() {
    let mut copy = Storage::new();
    copy.insert(Foo(42));

    let mut non_copy = Storage::new();
    non_copy.insert(Bar(vec![42]));
}
