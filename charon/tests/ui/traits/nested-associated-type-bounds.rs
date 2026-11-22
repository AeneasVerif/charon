//@ known-failure
pub trait Bound {}
pub trait Iter {
    type Item;
}
pub trait Tr {
    type A: Iter<Item: Bound>;
}
fn needs_bound<X: Bound>(_: &X) {}
fn needs_sized<X>() {}

pub fn direct<T: Tr>(x: <T::A as Iter>::Item) {
    needs_bound(&x)
}
pub fn with_clause<T: Tr>(x: <T::A as Iter>::Item)
where
    T::A: Iter,
{
    needs_bound(&x)
}
pub fn with_clause_after<T: Tr>(x: <T::A as Iter>::Item)
where
    T::A: Iter,
{
    needs_sized::<T::A>();
    needs_bound(&x)
}
