//@ charon-args=--monomorphize --ullbc --print-ullbc

trait Foo {
    fn foo(&self);
}

struct Bar;

impl Foo for Bar {
    fn foo(&self) {}
}

fn main() {
    let bar = Bar;
    let some_foo: &dyn Foo = &bar;
    some_foo.foo();
}
