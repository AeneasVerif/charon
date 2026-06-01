//@ known-failure
//@ charon-args=--monomorphize

pub trait Trait {
    fn method(&self) -> usize;
}

impl<T> Trait for T {
    fn method(&self) -> usize {
        0
    }
}

pub fn f(x: &()) -> &dyn Trait {
    x
}
