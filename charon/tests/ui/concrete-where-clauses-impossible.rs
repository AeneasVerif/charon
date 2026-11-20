//@ charon-args=--monomorphize
//@ known-failure
#![feature(trivial_bounds)]
pub struct Env;
pub trait Unix {}

pub fn foo()
where
    Env: Unix,
{
}
pub fn bar()
where
    Env: Unix,
{
    foo()
}

pub trait Tr {
    fn method(&self);
}
impl Tr for Env
where
    Env: Unix,
{
    fn method(&self) {
        foo()
    }
}

// Clauses that hold don't prevent monomorphization.
pub fn holds()
where
    u32: Copy,
{
}
