//@ known-failure
//@ charon-args=--remove-associated-types=*
// Fails because of bad handling of `Self` clauses. Should be fixed by
// https://github.com/AeneasVerif/charon/pull/514.
#![feature(unboxed_closures)]

trait Trait {
    type Foo: Fn();
    fn call(&self) -> <Self::Foo as FnOnce<()>>::Output;
}

impl<F: Fn()> Trait for F {
    type Foo = F;
    fn call(&self) -> <Self::Foo as FnOnce<()>>::Output {
        self()
    }
}

fn use_foo() -> <<fn() as Trait>::Foo as FnOnce<()>>::Output {}
