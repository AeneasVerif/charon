#![feature(core_intrinsics, core_intrinsics_fallbacks)]
#![allow(internal_features)]

/// Multiply two `u128`s.
pub fn mult_u128(a: u128, b: u128) -> u128 {
    // If a target doesn't implement a given built-in operation, rustc has Rust implementations of
    // them that serve as replacement. This is normally handled invisibly during codegen, but
    // Charon doesn't have give access to that stage. Instead, we go find these routines in
    // `intrinsics::fallback`, which requires nightly Rust.
    use core::intrinsics::fallback::CarryingMulAdd;
    CarryingMulAdd::carrying_mul_add(a, b, 0, 0).0
}
