//@ charon-args=--hide-marker-traits
//! Reproduces a crash when substituting variables with the `--hide-marker-traits` option.
trait Idx {}

pub struct IndexVec<I>
where
    I: Idx,
{
    i: I,
}

pub struct Vector<I>
where
    I: Idx,
{
    vector: IndexVec<I>,
}
