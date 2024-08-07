//@ known-failure
use std::ops::Deref;

trait PointerFamily {
    type Pointer<T>: Deref<Target = T>;

    fn new<T>(value: T) -> Self::Pointer<T>;
}

struct BoxFamily;

impl PointerFamily for BoxFamily {
    type Pointer<T> = Box<T>;

    fn new<T>(value: T) -> Self::Pointer<T> {
        Box::new(value)
    }
}

fn make_pointer<F: PointerFamily, T>(x: T) -> F::Pointer<T> {
    F::new(x)
}

fn main() {
    let _: Box<_> = make_pointer::<BoxFamily, _>(42);
}

mod moar_variables {
    // Dummy trait to check we handle variables in clauses correctly.
    trait Link<T> {}
    impl<T, U> Link<T> for U {}

    trait Trait<T> {
        type Type<U>: Link<T>;
    }

    struct Foo;
    impl<T> Trait<Option<T>> for Foo {
        type Type<U> = (T, U);
    }
}
