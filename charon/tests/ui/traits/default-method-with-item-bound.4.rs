trait Has<T> {}

trait Trait {
    type Item;

    fn provided<P>(&mut self)
    where
        P: Has<Self::Item>,
        Self: Exact;
}

trait Exact: Trait {}

struct Empty<T>(T);

impl<T> Trait for Empty<T> {
    type Item = T;

    fn provided<P>(&mut self)
    where
        P: Has<Self::Item>,
        Self: Exact,
    {
    }
}
