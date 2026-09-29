//@ charon-arg=--start-from=crate::Counter::bump

pub struct Counter {
    pub n: u32,
}

impl Counter {
    pub fn bump(&self) -> u32 {
        self.n.wrapping_add(1)
    }
}

pub fn free_bump(c: &Counter) -> u32 {
    c.n.wrapping_add(1)
}
