//@ charon-args=--remove-adt-clauses
//@ charon-args=--remove-associated-types=__no_match__
// `--remove-associated-types` is passed a non-matching pattern so the trait associated types
// stay in place, exercising the "preserve" path.
//
// Regression test (companion to `remove-adt-clauses-supertrait.rs`): when a closure inherits a
// clause to a trait with associated types, the closure ADT itself becomes "untouchable" --
// its clauses are preserved and no dangling `Clause(var)` refs appear inside its
// `ItemSource::Closure { info }`. So `enter_trait_ref`'s rewrite path is *not* exercised for
// this closure, and the FnOnce trait_impl signature retains its original `Clause(var)`
// references intact.
//
// `remove-adt-clauses-supertrait.rs` covers the symmetric case (closure with a no-assoc-types
// clause, where dangling refs *do* get rewritten); together they pin both branches.

trait HasAssoc {
    type Output;
}

fn make_closure<T: HasAssoc>(x: T) -> impl FnOnce() {
    move || {
        let _ = x;
    }
}
