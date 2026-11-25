//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
#![feature(impl_restriction)]

trait Tr {
    fn f();
}

#[cfg(target_arch = "x86_64")]
impl Tr for u8 {
    fn f() {}
}
impl Tr for () {
    fn f() {
        mod m {
            pub impl(self) trait T {}
        }
    }
}
