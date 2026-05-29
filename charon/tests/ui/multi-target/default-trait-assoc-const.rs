//@ charon-args=--targets=x86_64-apple-darwin,aarch64-apple-darwin
trait Trait {
    const VALUE: usize = 1;
}

impl Trait for () {}
