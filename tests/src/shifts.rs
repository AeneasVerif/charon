//! Exercise the translation of bit shifts

pub fn shift_u32(a: u32) -> u32 {
    let i: usize = 16;
    let mut t = a >> i;
    t <<= i;
    t
}

pub fn shift_i32(a: i32) -> i32 {
    let i: isize = 16;
    let mut t = a >> i;
    t <<= i;
    t
}
