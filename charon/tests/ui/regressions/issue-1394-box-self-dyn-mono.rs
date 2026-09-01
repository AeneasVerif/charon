//@ charon-args=--monomorphize

trait Trait {
    fn method(self: Box<Self>);
}

struct S;

impl Trait for S {
    fn method(self: Box<Self>) {}
}

fn main() {
    let b: Box<dyn Trait> = Box::new(S);
    b.method();
}
