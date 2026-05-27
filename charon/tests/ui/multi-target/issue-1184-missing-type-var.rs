//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
pub struct Foo<T>(core::marker::PhantomData<T>);

impl<T> Foo<T> {
    pub fn bar() {
        loop {}
    }
}
