//@ known-failure

pub trait Supertrait<T> {}

pub trait WithAssoc {
    type Assoc;
}

pub trait Trait<P: WithAssoc>: Supertrait<P::Assoc> {}

pub fn use_trait<P>(_: &dyn Trait<P>) {}

fn main() {}
