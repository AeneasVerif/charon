//@ charon-args=--include core::intrinsics
//@ charon-args=--include core::any::_::of
#![feature(core_intrinsics)]
use std::any::TypeId;
use std::intrinsics;

fn main() {
    // Has a fallback body marked `#[miri::intrinsic_fallback_is_spec]`.
    let _ = intrinsics::select_unpredictable(true, 1u32, 2u32);
    // Has a fallback body that isn't the spec.
    let _ = intrinsics::ub_checks();
    // Has no fallback body.
    let _ = intrinsics::black_box(0u8);
    // We give it a custom fallback.
    let _ = TypeId::of::<u32>();
}
