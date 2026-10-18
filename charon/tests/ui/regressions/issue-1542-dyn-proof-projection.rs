//@ known-failure
use std::ops::Deref;

trait Trait {}

struct Wrap<P>(P);

impl<P: Deref> Trait for Wrap<P> where P::Target: Trait {}

fn use_trait<T: Trait>(_: T) {}

fn pass_to_wrap(p: &dyn Trait) {
    use_trait(Wrap(p));
}
