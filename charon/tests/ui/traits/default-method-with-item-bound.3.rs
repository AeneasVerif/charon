trait HasAssoc<T> {
    type Assoc;
}

trait Trait {
    type Item;
    fn defaulted<P>(&self)
    where
        P: HasAssoc<Self::Item, Assoc = bool>,
        Self: Exact,
    {
    }
}

trait Exact: Trait {}

struct Empty<T>(T);

impl<T> Trait for Empty<T> {
    type Item = T;
}
