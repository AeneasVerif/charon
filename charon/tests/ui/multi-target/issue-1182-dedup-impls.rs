//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
pub trait Foo {
    fn method() -> u32;
}

pub struct Struct;

#[cfg(target_pointer_width = "64")]
impl Foo for Struct {
    fn method() -> u32 {
        64
    }
}

#[cfg(target_pointer_width = "32")]
impl Foo for Struct {
    fn method() -> u32 {
        32
    }
}

pub fn call_method() -> u32 {
    <Struct as Foo>::method()
}
