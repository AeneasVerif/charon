//@ charon-args=--monomorphize

pub trait Trait {
    fn method(&self);
}

impl<T> Trait for &T {
    fn method(&self) {}
}

pub fn f<'a>(x: &'a &'a u32) -> &'a dyn Trait {
    x
}
