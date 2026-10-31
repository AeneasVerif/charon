//@ charon-args=--lift-associated-types=*
pub trait Lang {
    type B;
}
pub trait Values: Lang<B: Typed<V = Self>> {}
pub trait Typed {
    type V: Values;
}
pub fn f<T: Typed>(_: &<T::V as Lang>::B) {}
