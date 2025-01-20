//@ known-failure
trait Trait {
    fn method()
    where
        Self: Sized;
}

impl Trait for () {
    fn method() {}
}

fn main() {
    <() as Trait>::method()
}
