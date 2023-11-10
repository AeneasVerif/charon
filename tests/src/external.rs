//! This module uses external types and functions

use std::vec::Vec;

/// This function uses an external function
pub fn swap<'a, T>(x: &'a mut T, y: &'a mut T) {
    std::mem::swap(x, y)
}

/// This function uses external types and functions
pub fn test_new_non_zero_u32(x: u32) -> std::num::NonZeroU32 {
    std::num::NonZeroU32::new(x).unwrap()
}

/// TODO: make vec external (rather than primitive)
#[allow(clippy::vec_init_then_push)]
pub fn test_vec() {
    let mut v: Vec<u32> = Vec::new();
    v.push(0);
}

/// Playing with a function in a state-error monad and which needs
/// forward and backward translations.
pub fn custom_swap<'a, T>(x: &'a mut T, y: &'a mut T) -> &'a mut T {
    std::mem::swap(x, y);
    x
}

pub fn test_custom_swap<'a>(x: &'a mut u32, y: &'a mut u32) {
    let z = custom_swap(x, y);
    *z = 1;
}

/// We just want a stateful example with a panic
pub fn test_swap_non_zero(mut x: u32) -> u32 {
    let mut y = 0;
    swap(&mut x, &mut y);

    if x == 0 {
        panic!();
    } else {
        x
    }
}
