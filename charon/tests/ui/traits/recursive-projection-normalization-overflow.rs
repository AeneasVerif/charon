//@ known-failure
//@ rustc-args=-Znext-solver=coherence

trait Query {}

trait AsQuery {
    type Query: Query;
}

impl<T: Query> AsQuery for T {
    type Query = Self;
}

trait Table: AsQuery {}

trait FilterDsl<P> {
    type Output;
}

type Filter<S, P> = <S as FilterDsl<P>>::Output;

impl<T: Table, P> FilterDsl<P> for T
where
    T::Query: FilterDsl<P>,
{
    type Output = Filter<T::Query, P>;
}

struct ConcreteQuery;
impl Query for ConcreteQuery {}

impl<P> FilterDsl<P> for ConcreteQuery {
    type Output = ();
}

fn main() {}
