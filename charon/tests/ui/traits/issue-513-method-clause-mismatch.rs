trait Trait: Sized {
    fn method<T: Copy>(self, other: T);
}

impl Trait for () {
    // This implementation is more general because it works for non-`Copy` `T`s.
    fn method<T>(self, _other: T) {}
}

fn main() {
    let _ = ().method(false);
    // We can't actually use the relaxed bound today.
    // #[derive(Clone)]
    // struct Foo;
    // let _ = ().method(Foo);
}
