//@ charon-args=--eager-vtables
//! With `--eager-vtables`, the vtable of `impl Foo for ()` is translated even though it is never
//! used in an unsizing. The `Debug` impl's vtable is unknown because `core::fmt` is excluded.
trait Foo {
    fn bar(&self);
}

#[derive(Debug)]
struct S;

impl Foo for () {
    fn bar(&self) {}
}

fn main() {
    ().bar();
}
