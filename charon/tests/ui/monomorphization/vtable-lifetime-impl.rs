//@ known-failure
//@ charon-args=--monomorphize

pub trait Trait {
    fn method(&self);
}

pub struct Pattern<'a>(&'a str);

impl Trait for Pattern<'_> {
    fn method(&self) {}
}

pub fn f<'a>(x: &'a Pattern<'a>) -> &'a dyn Trait {
    x
}
