//@ known-failure
//@ charon-args=--lift-associated-types=*
#![no_std]

// Regression test for https://github.com/AeneasVerif/charon/issues/1260.
// A self-referential associated type (via its bound) made the lift pass panic with
// `GenericsMismatch` while building the "could not compute / --exclude" diagnostic.
// We now emit the diagnostic gracefully instead of panicking.
pub trait Ring {
    type PrimeSubfield: PrimeField;
    const ZERO: Self;
}
pub trait Field: Ring {
    type Packing;
}
pub trait PrimeField: Field {}

pub fn sub_field_zero<R: Ring>() -> R::PrimeSubfield {
    R::PrimeSubfield::ZERO
}
