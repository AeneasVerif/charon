//@ charon-args=--consts=values

pub const SIMPLE: u32 = 42;
pub const COMPUTED: u32 = SIMPLE + 1;
pub const PAIR: (u32, bool) = (COMPUTED, true);
pub const ARRAY: [u8; 3] = [1, 2, 3];
pub static STATIC: u32 = 100;
pub struct Node(&'static Node);
pub static REC_A: Node = Node(&REC_B);
pub static REC_B: Node = Node(&REC_A);

trait HasLen {
    const LEN: usize;
}

impl<T> HasLen for [T; 4] {
    const LEN: usize = 4;
}

pub fn use_consts() -> u32 {
    SIMPLE + COMPUTED + STATIC
}
