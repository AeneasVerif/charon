//@ charon-args=--evaluate-consts
//! Test the `--evaluate-consts` flag: named constants and statics are evaluated into values
//! instead of keeping a call to their initializer function. Generic constants can't be evaluated
//! in polymorphic mode, so they keep their initializer call.

// Evaluates to `42`.
pub const SIMPLE: u32 = 42;

// Evaluates to `43` (the initializer is not kept).
pub const COMPUTED: u32 = SIMPLE + 1;

// Evaluates to an aggregate value.
pub const PAIR: (u32, bool) = (COMPUTED, true);

// Evaluates to an array.
pub const ARRAY: [u8; 3] = [1, 2, 3];

// A static, evaluated through `static_value`.
pub static STATIC: u32 = 100;

// Two mutually-recursive statics: each holds a (shared) pointer to the other. These still
// evaluate: the cycle is broken by reference, so each value is a struct holding a reference to the
// other static (rather than recursing forever or falling back to an initializer call).
pub struct Node(&'static Node);
pub static REC_A: Node = Node(&REC_B);
pub static REC_B: Node = Node(&REC_A);

// A generic associated const: can't be evaluated polymorphically, so it keeps its initializer
// call.
trait HasLen {
    const LEN: usize;
}

impl<T> HasLen for [T; 4] {
    const LEN: usize = 4;
}

pub fn use_consts() -> u32 {
    SIMPLE + COMPUTED + STATIC
}
