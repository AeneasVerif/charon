//@ charon-args=--monomorphize
// Ensures monomorphization happens when trait implementations are involved.

use std::mem;

fn do_test<T: std::cmp::Eq>(init: T, expected: T) {
    assert!(expected == init);
}

fn main() {
    do_test::<bool>(true, true);
}
