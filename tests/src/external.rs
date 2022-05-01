//! This module uses external types and functions
#![allow(dead_code)]

use std::vec::Vec;

/// This function uses an external function
fn swap<'a, T>(x: &'a mut T, y: &'a mut T) {
    std::mem::swap(x, y)
}

/// This function uses external types and functions
fn test_new_non_zero_u32(x: u32) -> std::num::NonZeroU32 {
    std::num::NonZeroU32::new(x).unwrap()
}

/// TODO: make vec external (rather than primitive)
fn test_vec() {
    let mut v: Vec<u32> = Vec::new();
    v.push(0);
}

/// Playing with a function in a state-error monad and which needs
/// forward and backward translations.
fn custom_swap<'a, T>(x: &'a mut T, y: &'a mut T) -> &'a mut T {
    std::mem::swap(x, y);
    x
}

fn test_custom_swap<'a>(x: &'a mut u32, y: &'a mut u32) {
    let z = custom_swap(x, y);
    *z = 1;
}
