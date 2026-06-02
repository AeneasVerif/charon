//@ known-failure

pub trait QueryTrait {}

pub trait AsQuery {
    type Query: QueryTrait;
}

impl<T: QueryTrait> AsQuery for T {
    type Query = Self;
}

pub trait TableTrait: AsQuery {}

pub trait FilterDsl<Predicate> {
    type Output;
}

pub type Filter<Source, Predicate> = <Source as FilterDsl<Predicate>>::Output;

impl<T, Predicate> FilterDsl<Predicate> for T
where
    T: TableTrait,
    T::Query: FilterDsl<Predicate>,
{
    type Output = Filter<T::Query, Predicate>;
}

fn main() {}
