//@ charon-args=--remove-associated-types=*
#![feature(associated_type_defaults)]

// Regression test for https://github.com/AeneasVerif/charon/issues/1078.
trait Foo<'a, T: 'a> {
    type X: 'a;
    type Item = &'a (T, Self::X);
}

impl<'a, T: 'a> Foo<'a, Option<T>> for () {
    type X = &'a ();
}
