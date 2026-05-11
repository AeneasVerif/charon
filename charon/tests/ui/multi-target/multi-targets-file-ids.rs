//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
//! Regression test for multi-target file-id remapping.
//!
//! When merging per-target crates, files unique to some targets get pushed into the
//! merged file table at new positions: the corresponding file ids need to be properly
//! updated.
//!
//! This test uses enough architecture-specific intrinsics to pull in different header
//! files for each target.
#![allow(unused, non_camel_case_types)]

trait SimdOps {
    type V128: Copy;
    fn load(src: &[u16; 8]) -> Self::V128;
    fn store(dst: &mut [u16; 8], val: Self::V128);
    fn add(a: Self::V128, b: Self::V128) -> Self::V128;
}

#[cfg(target_arch = "x86_64")]
mod x86 {
    use core::arch::x86_64::*;
    use super::SimdOps;

    pub struct Sse2;
    impl SimdOps for Sse2 {
        type V128 = __m128i;
        fn load(src: &[u16; 8]) -> __m128i {
            unsafe { _mm_loadu_si128(src.as_ptr() as *const __m128i) }
        }
        fn store(dst: &mut [u16; 8], val: __m128i) {
            unsafe { _mm_storeu_si128(dst.as_mut_ptr() as *mut __m128i, val) }
        }
        fn add(a: __m128i, b: __m128i) -> __m128i {
            unsafe { _mm_add_epi16(a, b) }
        }
    }
}

#[cfg(target_arch = "aarch64")]
mod arm {
    use core::arch::aarch64::*;
    use super::SimdOps;

    pub struct Neon;
    impl SimdOps for Neon {
        type V128 = uint16x8_t;
        fn load(src: &[u16; 8]) -> uint16x8_t {
            unsafe { vld1q_u16(src.as_ptr()) }
        }
        fn store(dst: &mut [u16; 8], val: uint16x8_t) {
            unsafe { vst1q_u16(dst.as_mut_ptr(), val) }
        }
        fn add(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
            unsafe { vaddq_u16(a, b) }
        }
    }
}

fn add_generic<T: SimdOps>(a: &mut [u16; 8], b: &[u16; 8]) {
    let va = T::load(a);
    let vb = T::load(b);
    T::store(a, T::add(va, vb));
}

fn add_scalar(a: &mut [u16; 8], b: &[u16; 8]) {
    for i in 0..8 {
        a[i] = a[i].wrapping_add(b[i]);
    }
}

fn cpu_features_present(_mask: u32) -> bool { true }

fn add_dispatch(a: &mut [u16; 8], b: &[u16; 8]) {
    #[cfg(target_arch = "x86_64")]
    {
        if cpu_features_present(1) {
            add_generic::<x86::Sse2>(a, b);
        } else {
            add_scalar(a, b);
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        if cpu_features_present(2) {
            add_generic::<arm::Neon>(a, b);
        } else {
            add_scalar(a, b);
        }
    }
}
