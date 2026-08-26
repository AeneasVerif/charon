#[inline(always)]
pub fn identical(x: u32) -> u32 {
    x ^ 0xdead_beef
}

#[track_caller]
pub fn also_identical(x: u32) -> u32 {
    x.wrapping_mul(3)
}
