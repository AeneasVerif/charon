pub trait HasAssoc1 {
    type Assoc1;
}

pub trait HasAssoc2 {
    type Assoc2;
}

pub trait Trait {
    type Item;
    // Mimics the kind of bound on `Iterator::try_collect`.
    fn defaulted(&self) -> <<Self::Item as HasAssoc1>::Assoc1 as HasAssoc2>::Assoc2
    where
        Self::Item: HasAssoc1<Assoc1: HasAssoc2>,
    {
        loop {}
    }
}

pub struct Empty<T>(T);
impl<T> Trait for Empty<T> {
    type Item = T;
}

impl Trait for () {
    type Item = ();
}
