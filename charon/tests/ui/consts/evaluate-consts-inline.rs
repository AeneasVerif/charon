//@ charon-args=--evaluate-consts
//! Const inlining: inline/promoted constants are inlined into their use site. Promoted constants
//! flow through `anon_const_to_call` (which turns the reference into a call to the constant's
//! initializer) and `inline_selected_functions` (which inlines that initializer). Inline const
//! blocks are evaluated and inlined by hax during translation. This is unaffected by
//! `--evaluate-consts` for these forms (promoteds aren't const-evaluated).

// A promoted constant: `&42` promotes `42` to an anonymous constant and borrows it.
pub fn promoted_scalar() -> &'static i32 {
    const { &42 }
}

// A promoted array constant.
pub fn promoted_array() -> &'static [i32; 3] {
    const { &[1, 2, 3] }
}

// An inline const block.
pub fn inline_block() -> u32 {
    const { 2 + 3 }
}

// An inline const block of an aggregate type.
pub fn inline_pair() -> (u32, u32) {
    const { (1, 2) }
}
