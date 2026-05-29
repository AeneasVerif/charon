//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
#[charon::opaque]
trait Trait {
    fn method1(&self) {}
    fn method2(&self) {}
    fn method3(&self) {}
}

#[cfg(target_arch = "x86_64")]
fn f(x: &impl Trait) {
    x.method1()
}

#[cfg(target_arch = "aarch64")]
fn g(x: &impl Trait) {
    x.method2()
}
