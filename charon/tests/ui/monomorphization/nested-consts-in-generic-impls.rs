//@ charon-args=--monomorphize --start-from=crate::main

struct Wrapper<T>(T);

impl<T> Wrapper<T> {
    fn inherent() -> u8 {
        const VALUE: u8 = 1;
        VALUE
    }
}

trait Trait {
    fn method() -> u8;
}

impl<T> Trait for Wrapper<T> {
    fn method() -> u8 {
        const VALUE: u8 = 2;
        VALUE
    }
}

fn main() {
    Wrapper::<u8>::inherent();
    <Wrapper<u16> as Trait>::method();
}
