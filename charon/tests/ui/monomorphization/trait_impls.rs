//@ charon-args=--monomorphize --ullbc --print-ullbc --no-serialize --translate-all-methods

use std::mem;

fn do_test<T: std::cmp::Eq>(init: T, expected: T) {
    assert!(expected == init);
}

fn main() {
    do_test::<bool>(true, true);
}
