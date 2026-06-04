//@ charon-args=--monomorphize
pub trait Foo {
    fn bar() {}
}

impl Foo for u8 {}

fn main() {
    <u8 as Foo>::bar();
}
