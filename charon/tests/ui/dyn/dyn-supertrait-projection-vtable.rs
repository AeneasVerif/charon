//@ known-failure

trait Foo {
    type V;
}

trait Super<X> {
    type A;
}

trait Callback<T: Foo>: Super<T::V, A = ()> {}

struct Bar<T: Foo> {
    callback: Box<dyn Callback<T>>,
}

fn main() {}
