//@ known-failure
//@ charon-args=--lift-associated-types=_
pub trait Foo {
    type Size: Copy;
}

pub trait Bar {
    type Item<T>: Foo;
}
