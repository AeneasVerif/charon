/// Only reachable from `crate_b::entry`.
pub fn used() -> u32 {
    0
}

/// Not reachable from the start-from items.
pub fn unused() -> u32 {
    0
}

pub trait Describe {
    fn describe(&self) -> u32;
}
