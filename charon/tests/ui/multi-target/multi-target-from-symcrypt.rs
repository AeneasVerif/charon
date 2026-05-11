//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
#![allow(unused, non_camel_case_types)]

// ── Trait abstracting over platform SIMD intrinsics ────────────────────

trait NttIntrinsicsInterface {
    type Vec128: Copy;

    fn vec128_load(src: &[u16; 8]) -> Self::Vec128;
    fn vec128_store(dst: &mut [u16; 8], val: Self::Vec128);
    fn vec128_add(a: Self::Vec128, b: Self::Vec128) -> Self::Vec128;
}

// ── x86_64 backend ────────────────────────────────────────────────────

#[cfg(target_arch = "x86_64")]
mod ntt_xmm {
    use super::NttIntrinsicsInterface;
    use core::arch::x86_64::*;

    pub struct NttIntrinsicsXmm;

    impl NttIntrinsicsInterface for NttIntrinsicsXmm {
        type Vec128 = __m128i;

        fn vec128_load(src: &[u16; 8]) -> __m128i {
            unsafe { _mm_loadu_si128(src.as_ptr() as *const __m128i) }
        }
        fn vec128_store(dst: &mut [u16; 8], val: __m128i) {
            unsafe { _mm_storeu_si128(dst.as_mut_ptr() as *mut __m128i, val) }
        }
        fn vec128_add(a: __m128i, b: __m128i) -> __m128i {
            unsafe { _mm_add_epi16(a, b) }
        }
    }
}

// ── aarch64 backend ───────────────────────────────────────────────────

#[cfg(target_arch = "aarch64")]
mod ntt_neon {
    use super::NttIntrinsicsInterface;
    use core::arch::aarch64::*;

    pub struct NttIntrinsicsNeon;

    impl NttIntrinsicsInterface for NttIntrinsicsNeon {
        type Vec128 = uint16x8_t;

        fn vec128_load(src: &[u16; 8]) -> uint16x8_t {
            unsafe { vld1q_u16(src.as_ptr()) }
        }
        fn vec128_store(dst: &mut [u16; 8], val: uint16x8_t) {
            unsafe { vst1q_u16(dst.as_mut_ptr(), val) }
        }
        fn vec128_add(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
            unsafe { vaddq_u16(a, b) }
        }
    }
}

// ── Generic (scalar) fallback ─────────────────────────────────────────

fn ntt_layer_generic(a: &mut [u16; 8], b: &[u16; 8]) {
    for i in 0..8 {
        a[i] = a[i].wrapping_add(b[i]);
    }
}

// ── Vectorised implementation, generic over the intrinsics trait ──────

fn ntt_layer_vec128<T: NttIntrinsicsInterface>(a: &mut [u16; 8], b: &[u16; 8]) {
    let va = T::vec128_load(a);
    let vb = T::vec128_load(b);
    let vr = T::vec128_add(va, vb);
    T::vec128_store(a, vr);
}

// ── Portable entry point: cfg-dispatched ──────────────────────────────

const SYMCRYPT_CPU_FEATURE_SSE2: u32 = 0x01;
const SYMCRYPT_CPU_FEATURE_NEON: u32 = 0x02;

fn cpu_features_present(_mask: u32) -> bool {
    true
}

fn poly_element_ntt_layer(a: &mut [u16; 8], b: &[u16; 8]) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        if cpu_features_present(SYMCRYPT_CPU_FEATURE_SSE2) {
            ntt_layer_vec128::<ntt_xmm::NttIntrinsicsXmm>(a, b);
        } else {
            ntt_layer_generic(a, b);
        }
    }

    #[cfg(target_arch = "aarch64")]
    {
        if cpu_features_present(SYMCRYPT_CPU_FEATURE_NEON) {
            ntt_layer_vec128::<ntt_neon::NttIntrinsicsNeon>(a, b);
        } else {
            ntt_layer_generic(a, b);
        }
    }
}
