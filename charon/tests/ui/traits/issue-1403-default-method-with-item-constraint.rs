//@ no-default-options
//@ charon-args=--translate-all-methods
//@ charon-args=--lift-associated-types=*
pub struct A;
pub struct B;

pub trait Trait {
    type Assoc;

    fn method(&self)
    where
        Self: Trait<Assoc = B>,
    {
    }
}

impl Trait for () {
    type Assoc = A;
}
