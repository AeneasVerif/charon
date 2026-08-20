//@ charon-args=--remove-associated-types=*
//! Regression test for https://github.com/AeneasVerif/charon/issues/1078.
#![feature(associated_type_defaults)]

trait Foo<T> {
    type X;
    type Item = (T, Self::X);
}

impl<T> Foo<Option<T>> for () {
    type X = ();
}
