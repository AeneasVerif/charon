//@ charon-args=--extract-opaque-bodies --hide-marker-traits
#![feature(core_intrinsics, core_intrinsics_fallbacks)]
#![allow(internal_features)]

use core::intrinsics::fallback::CarryingMulAdd;

pub fn mult_u128(a: u128, b: u128) -> u128 {
    CarryingMulAdd::carrying_mul_add(a, b, 0, 0).0
}
