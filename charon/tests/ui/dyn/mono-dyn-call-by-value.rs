//@ no-default-options
//@ charon-args=--monomorphize

// this could be Box<dyn FnOnce> but it would make the output a pain
// to read, so we re-do it by hand instead.

#![feature(unsized_fn_params)]
trait T {
    fn by_ref(&self);
    fn by_val(self);
}
impl T for () {
    fn by_ref(&self) {}
    fn by_val(self) {}
}

struct Foo<T: ?Sized>(T);

fn main() {
    let b: Box<dyn T> = Box::new(());
    b.by_ref();
    (*b).by_val();

    let f: Box<Foo<dyn T>> = Box::new(Foo(()));
    f.0.by_ref();
    ((*f).0).by_val();
}
