//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize

pub struct Wrapper<T>(T);

pub trait Parent<T> {}

pub trait Child<T>: Parent<Wrapper<T>> {}

impl Parent<Wrapper<u8>> for () {}

impl Child<u8> for () {}
