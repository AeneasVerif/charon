//@ no-default-options
//@ charon-args=--ullbc --print-ullbc
//@ charon-args=--reconstruct-fallible-operations
//! Regression test for issue #1041: rustc evaluates the shift operands (and emits the overflow
//! check) before computing the destination place, so when that computation involves a call (here
//! the overloaded `index_mut`), the shift ends up in the block the call returns to. The check
//! must still be reconstructed into a panic-on-overflow shift.
use std::ops::IndexMut;

pub struct Wrap(pub [u64; 2]);

impl std::ops::Index<usize> for Wrap {
    type Output = u64;
    fn index(&self, i: usize) -> &u64 {
        &self.0[i]
    }
}
impl IndexMut<usize> for Wrap {
    fn index_mut(&mut self, i: usize) -> &mut u64 {
        &mut self.0[i]
    }
}

pub fn shr_into_index(x: u64, out: &mut Wrap) {
    out[0] = x >> 20;
}

pub fn shl_into_index_by_var(x: u64, n: u32, out: &mut Wrap) {
    out[1] = x << n;
}
