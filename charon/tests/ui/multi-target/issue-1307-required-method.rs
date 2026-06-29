//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
pub struct Foo;

impl Clone for Foo {
    fn clone(&self) -> Self {
        loop {}
    }
}
