# rustc_trait_elaboration

`rustc_trait_elaboration` is a subcrate of Charon, in charge of all the "trait proofs" logic (TODO:
there should be a chapter explaining that). It's meant to be a sort of extension to internal rustc
APIs, hence the name.

The two main building blocks are:
- `TraitProof` represents a trait proof object;
- `ItemRef` is a reference to an item, identified by an `Id` and `GenericArgs`. The whole point of
  the crate is that we also compute a list of `TraitProof`s, which prove the item's required predicates.

The crate is generic over the `Id` type used to identify items. It's meant to be just like rustc's
`DefId`, but we do add fake extra `Id`s that don't correspond to one, so the crate was made generic
to support that.

Each provable predicate is identified by its `ItemPredicateId`. `ItemPredicates` contains the logic
for computing which predicates each item has. This is the source of truth used everywhere else.

The important notion here is "required" vs "implied" predicates.
Required predicates are those that must hold whenever we mention an item. E.g. `fn foo<T: Clone>`
has a `T: Clone` required predicate. Most of them are like that.
Implied predicates are those that we can derive from an item. These only occur in traits,
and all `where` clauses of a trait as well as item bounds are implied.

The crate is a bit ad-hoc, it uses rustc APIs that aren't meant to be used like that probably.
Ideally we'd transition to using rustc's recently-added "proof trees",
see <https://github.com/AeneasVerif/charon/issues/1038>.
