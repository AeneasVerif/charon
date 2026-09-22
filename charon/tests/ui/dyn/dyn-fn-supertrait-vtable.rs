//@ known-failure

trait Foo {
    type V;
}

trait Callback<T: Foo>: Fn(&T, &T::V) {}

struct Bar<T: Foo> {
    callback: Box<dyn Callback<T>>,
}

fn main() {}
