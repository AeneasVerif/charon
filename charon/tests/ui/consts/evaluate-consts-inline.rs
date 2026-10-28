//@ charon-args=--consts=values

pub fn promoted_scalar() -> &'static i32 {
    &42
}

pub fn promoted_array() -> &'static [i32; 3] {
    &[1, 2, 3]
}

pub fn promoted_local() -> i32 {
    let r = &(2 + 3);
    *r
}

pub fn inline_ref_scalar() -> &'static i32 {
    const { &42 }
}

pub fn inline_ref_array() -> &'static [i32; 3] {
    const { &[1, 2, 3] }
}

pub fn inline_block() -> u32 {
    const { 2 + 3 }
}

pub fn inline_pair() -> (u32, u32) {
    const { (1, 2) }
}

static S: i32 = 1;
pub fn inline_ref_static() -> &'static i32 {
    const { &S }
}

pub fn promoted_bools() -> &'static [bool; 2] {
    &[true, false]
}

pub fn promoted_chars() -> &'static [char; 2] {
    &['a', '🦀']
}

pub fn promoted_str() -> &'static str {
    "hello"
}

#[repr(C)]
pub struct P {
    a: u8,
    b: u16,
}
// Byte 1 is padding for `P`, but it is initialized in the allocation.
pub const PADDED: &P = unsafe { &*(&0x0403_0201u32 as *const u32 as *const P) };
