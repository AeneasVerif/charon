//@ charon-args=--remove-associated-types=*
//! Regression test for https://github.com/AeneasVerif/charon/issues/1078.
//! When a defaulted associated type is instantiated for an impl, the proofs it uses become
//! self-referential. This can cause `--remove-associated-types` to loop forever, if we're not
//! careful.
#![feature(associated_type_defaults)]

struct Tuple<A, B: ?Sized>(A, B);

trait ProveWithParentClause<T> {
    type X;
    type Item = Tuple<T, Self::X>;
}

impl<T> ProveWithParentClause<Option<T>> for () {
    type X = ();
}

trait ProveWithItemClause<T> {
    type X;
    type Item = Tuple<Self::X, T>;
}

impl<T> ProveWithItemClause<Option<T>> for () {
    type X = ();
}
