//@ charon-args=--consts=values

// A constant/static that genuinely cannot be evaluated to a value because of recursiveness.

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
