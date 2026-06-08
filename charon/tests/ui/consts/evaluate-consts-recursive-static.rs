//@ charon-args=--evaluate-consts
//! A constant/static that genuinely cannot be evaluated to a value because of recursiveness.
//!
//! Forming a *mutable* cycle requires interior mutability (`Cell`): the two statics below point at
//! each other through `Cell`s. Because their memory is mutable, rustc won't expose them as
//! constant values, so `--evaluate-consts` can't evaluate them and they keep a call to their
//! initializer (unlike the immutable, shared-reference cycle in `evaluate-consts.rs`, which does
//! evaluate).
//!
//! This also exercises a subtle fallback path: evaluating the static steals its promoted MIR, so
//! the initializer body must then be fetched via `mir_for_ctfe` rather than `optimized_mir` (which
//! panics on statics). See `get_mir.rs`.

use core::cell::Cell;

pub struct Node {
    value: u32,
    next: Cell<&'static Node>,
}
unsafe impl Sync for Node {}

pub static CYCLE_A: Node = Node {
    value: 1,
    next: Cell::new(&CYCLE_B),
};
pub static CYCLE_B: Node = Node {
    value: 2,
    next: Cell::new(&CYCLE_A),
};
