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
