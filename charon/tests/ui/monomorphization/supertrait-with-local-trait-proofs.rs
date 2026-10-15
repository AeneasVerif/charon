//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//@[mono] known-failure

pub trait Bound {}
impl Bound for u8 {}

pub struct Nested<T>(T);
impl<T: Bound> Bound for Nested<T> {}

pub struct Wrapper<T: Bound>(T);
pub trait Parent<T> {}

pub trait Child: Parent<Wrapper<u8>> + Parent<Wrapper<Nested<u8>>>
where
    u8: Bound,
{
}

impl Parent<Wrapper<u8>> for () {}
impl Parent<Wrapper<Nested<u8>>> for () {}
impl Child for () {}
