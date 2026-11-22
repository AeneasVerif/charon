//@ known-failure
//@ charon-args=--lift-associated-types=*
pub trait Trait {
    type Output;
}

pub trait Deref {
    type Target: ?Sized;
}

impl Deref for () {
    type Target = dyn Trait<Output = u8>;
}

pub struct Wrap<P>(P);

impl<P: Deref> Trait for Wrap<P>
where
    P::Target: Trait,
{
    type Output = <P::Target as Trait>::Output;
}

pub fn assert_trait<F: Trait>(_: F) {}

pub fn f() {
    assert_trait(Wrap(()))
}
