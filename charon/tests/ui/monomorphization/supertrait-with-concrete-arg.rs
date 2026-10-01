//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
pub struct Concrete;
pub struct Wrapper<T>(T);

pub trait Parent<T: ?Sized> {}

pub trait Child: Parent<Concrete> + Parent<Wrapper<u8>> {}

impl Parent<Concrete> for () {}
impl Parent<Wrapper<u8>> for () {}
impl Child for () {}
