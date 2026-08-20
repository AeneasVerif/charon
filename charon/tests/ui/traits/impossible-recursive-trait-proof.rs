//@ known-failure
pub trait HasAssoc {
    type Assoc;
}

pub trait Trait<X>: HasAssoc {}

fn foo<T: Trait<<T as HasAssoc>::Assoc>>() {}
