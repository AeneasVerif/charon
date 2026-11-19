pub fn use_a(b: Box<u32>) -> u32 {
    crate_a::check(crate_a::unbox(b))
}

/// Its associated item names come after `crate_a`'s.
pub trait Shape {
    fn area(&self) -> u32;
}

impl Shape for u32 {
    fn area(&self) -> u32 {
        *self
    }
}
