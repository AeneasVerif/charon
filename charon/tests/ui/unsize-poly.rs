#![feature(unsize, coerce_unsized)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;

pub fn through_ref<T: ?Sized + Unsize<U>, U: ?Sized>(x: &T) -> &U {
    x
}

pub fn through_box<T: ?Sized + Unsize<U>, U: ?Sized>(x: Box<T>) -> Box<U> {
    x
}

pub struct Wrapper<P>(P);
impl<P: CoerceUnsized<Q>, Q> CoerceUnsized<Wrapper<Q>> for Wrapper<P> {}

pub fn through_coerce_unsized<P: CoerceUnsized<Q>, Q>(x: Wrapper<P>) -> Wrapper<Q> {
    x
}
