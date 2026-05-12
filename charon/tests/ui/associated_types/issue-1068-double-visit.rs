//@ charon-args=--lift-associated-types=*
//! Regression test: associated type lifting caused double-processing of type args.
pub struct Witness1;
pub struct Witness2;

pub trait HasType1 {
    type Type1;
}
impl HasType1 for Witness1 {
    type Type1 = ();
}

pub trait HasType2 {
    type Type2;
}
pub struct Comparator<A: HasType1>(A);
impl HasType2 for Witness2 {
    type Type2 = Comparator<Witness1>;
}

pub trait HasType3 {
    type Type3;
}
impl<T: HasType2> HasType3 for T {
    type Type3 = T::Type2;
}

fn check<D: HasType3>() {}
fn main() {
    check::<Witness2>()
}
