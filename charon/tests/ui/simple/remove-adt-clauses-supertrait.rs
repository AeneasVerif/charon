//@ charon-args=--remove-adt-clauses
//@ charon-args=--remove-associated-types=*
// Regression test: when `--remove-adt-clauses` strips a clause to a trait with supertraits, the
// synthesized `BuiltinOrAuto[RemovedAdtClause]` placeholder must include a recursive
// `RemovedAdtClause` parent ref for each supertrait, so the placeholder matches the trait's
// shape. The post-transformation typechecker checks this; if the recursion were missing or the
// counts wrong, this test would fail there.

trait GrandParent {}
trait Parent: GrandParent {}
trait Child: Parent {}

// The closure inherits `T: Child` from `make`, so after stripping, references to that clause
// inside the closure ADT become dangling and get rewritten to `RemovedAdtClause`. The recursive
// parent fill is exercised because `Child: Parent: GrandParent`.
fn make<T: Child>(x: T) -> impl FnOnce() {
    move || {
        let _ = x;
    }
}
