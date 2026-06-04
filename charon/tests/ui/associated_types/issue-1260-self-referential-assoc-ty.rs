//@ known-failure
//@ charon-args=--lift-associated-types=*
#![no_std]

pub trait Ring {
    type PrimeSubfield: Field;
    const ZERO: Self;
}
pub trait Field: Ring {
    type Packing;
}

pub fn sub_field_zero<R: Ring>() -> R::PrimeSubfield {
    R::PrimeSubfield::ZERO
}
