//@ output=run-with-minirust
//@ known-ub
// see https://github.com/AeneasVerif/charon/pull/1621

use std::sync::atomic::AtomicI32;

static X: (i32, AtomicI32) = (0, AtomicI32::new(1));

fn main() {
    let ptr = &raw const X;
    unsafe { ptr.cast_mut().write((1, AtomicI32::new(0))) }; // UB! Child write to Frozen
}
