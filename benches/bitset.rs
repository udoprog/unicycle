#![feature(test)]

extern crate test;

use test::Bencher;

static INDEXES: [usize; 12] = [
    0, 32, 64, 3030, 4095, 50_000, 102110, 203020, 411212, 500000, 803020, 900900
];

#[bench]
fn test_hibitset(b: &mut Bencher) {
    use hibitset::BitSet;

    let mut set = BitSet::with_capacity(1_000_000);

    for i in INDEXES.iter().copied() {
        set.add(i as u32);
    }

    b.iter(|| (&set).into_iter().collect::<Vec<_>>());
}

#[bench]
fn test_local_bitset(b: &mut Bencher) {
    use unicycle::BitSet;
    
    let mut set = BitSet::with_capacity(1_000_000);

    for i in INDEXES.iter().copied() {
        set.set(i);
    }

    b.iter(|| set.iter().collect::<Vec<_>>());
}