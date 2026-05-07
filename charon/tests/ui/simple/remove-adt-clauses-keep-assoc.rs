//@ charon-args=--remove-adt-clauses
//@ charon-args=--remove-associated-types=__no_match__
// `--remove-associated-types` is passed a non-matching pattern: it's required to be non-empty
// by `--remove-adt-clauses`'s validation, but here we want to leave the trait associated types
// alone so we can test the "preserve clause when trait has assoc types" path.
//
// Regression test: `--remove-adt-clauses` must NOT strip a clause when the trait it points at
// has an associated type (directly or via a transitive supertrait). Otherwise we'd have no way
// to synthesize a placeholder value for the associated type. We leave the whole ADT untouched.
//
// The marker trait at the bottom has no associated types anywhere in its supertrait chain, so
// its clause should still be stripped.

trait HasAssoc {
    type Output;
}

// `HasAssoc` has a direct associated type, so this clause must be kept.
struct Direct<T: HasAssoc>(T);

trait BaseWithAssoc {
    type Item;
}
trait DerivedNoAssoc: BaseWithAssoc {}

// `DerivedNoAssoc` has no direct associated type, but inherits one from `BaseWithAssoc` via the
// supertrait. The clause must still be kept (transitive case).
struct Transitive<T: DerivedNoAssoc>(T);

trait MarkerParent {}
trait MarkerChild: MarkerParent {}

// Pure marker inheritance, no associated types: this clause may safely be stripped.
struct Marker<T: MarkerChild>(T);

fn use_all<T: HasAssoc, U: DerivedNoAssoc, V: MarkerChild>(
    _x: Direct<T>,
    _y: Transitive<U>,
    _z: Marker<V>,
) {
}
