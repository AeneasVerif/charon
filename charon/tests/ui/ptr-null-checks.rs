//@ charon-args=--mir optimized --reconstruct-null-checks
//! Tests for the `reconstruct_ptr_null_checks` micro-pass, which rewrites a
//! `transmute::<*T, usize>(p)` that feeds a `switch [0, otherwise]` (the shape rustc emits when
//! lowering pointer null-checks) into a comparison against the null pointer.

// Should be rewritten: a thin pointer is transmuted to `usize`, switched against `0`, and the
// resulting value is used nowhere else.
pub fn check_raw(p: *mut u8) -> u32 {
    let x: usize = unsafe { core::mem::transmute(p) };
    match x {
        0 => 1,
        _ => 2,
    }
}

// Same, but through a shared reference and to `isize`.
pub fn check_ref(p: &u8) -> u32 {
    let x: isize = unsafe { core::mem::transmute(p) };
    match x {
        0 => 1,
        _ => 2,
    }
}

// Should NOT be rewritten: the transmuted value `x` is used after the switch, so replacing it with
// the address-erasing null-check would change the observable result.
pub fn other_use(p: *mut u8) -> usize {
    let x: usize = unsafe { core::mem::transmute(p) };
    let y = match x {
        0 => 1usize,
        _ => 2,
    };
    x.wrapping_add(y)
}
