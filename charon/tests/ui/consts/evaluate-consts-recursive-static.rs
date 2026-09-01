//@ charon-args=--consts=values

// Mutually-recursive statics. Evaluation terminates because a pointer to another static is
// recorded as a reference to that static, not by following it.

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
