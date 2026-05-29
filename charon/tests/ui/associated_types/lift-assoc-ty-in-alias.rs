//@ charon-args=--lift-associated-types=*
// Regression test for https://github.com/AeneasVerif/charon/issues/531.
pub trait HasAssoc {
    type Assoc;
}

pub type Alias<B> = <B as HasAssoc>::Assoc;
