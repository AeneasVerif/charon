//@ known-failure
//@ charon-args=--lift-associated-types=* --remove-unused-self-clauses

// Regression test for https://github.com/AeneasVerif/charon/issues/968.
pub trait ToU64 {
    fn to_u64(self) -> u64;
}

pub trait WithConstTy<const LEN: usize> {
    const LEN2: usize = 32;

    type W: ToU64;
}
