pub trait Trait1 {
    type T: Trait2;
}

pub trait Trait2: Trait1 {}

trait T1<T: T2<Self>>: Sized {}
trait T2<T: T1<Self>>: Sized {}
