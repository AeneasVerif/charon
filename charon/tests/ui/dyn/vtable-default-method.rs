pub trait Trait {
    fn base(&self) -> i32;
    fn dflt(&self) -> i32 {
        self.base() + 1
    }
}

pub struct Struct;

impl Trait for Struct {
    fn base(&self) -> i32 {
        1
    }
}

pub fn main() {
    let b: &dyn Trait = &Struct;
    let _ = b.dflt();
}
