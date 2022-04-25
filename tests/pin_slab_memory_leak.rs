use unicycle::pin_slab::PinSlab;

struct Foo(u32);

struct Bar(Vec<u32>);

#[global_allocator]
static ALLOCATOR: checkers::Allocator = checkers::Allocator::system();

#[checkers::test]
fn test_pin_slab_memory_leak() {
    let mut copy = PinSlab::new();
    copy.insert(Foo(42));

    let mut non_copy = PinSlab::new();
    non_copy.insert(Bar(vec![42]));
}
