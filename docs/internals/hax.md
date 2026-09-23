# Hax

Hax is a subcrate of Charon in charge of abstracting away most queries to rustc.
Charon initially merged its rustc queries logic with `hax-frontend` from
<https://github.com/cryspen/hax>, but eventually the usecases diverged sufficiently
that we forked hax-frontend into a subcrate of Charon and reworked it. The name is kept for now but
I'm thinking of renaming it to something like `rustc_frontend`.

The entrypoint of the crate is `FullDef`. A `FullDef` captures every single bit of useful
information about a rustc item, which Charon then translates into its more uniform representation.
It marks the boundary of rustc versus Charon: things that require rustc logic, like normalizing
types, evaluating constants or solving traits should be done in hax and exposed through `FullDef` as
much as possible.

The clever parts of hax are:
- Trait proof solving, using [`rustc_trait_elaboration`](./rustc_trait_elaboration.md);
- Constant evaluation and unevaluation, because rustc's constant representations are a bit complex;
- Monomorphization: `FullDef` can be created for a given item with or without a specific choice of
  generic arguments. If with arguments, then everything in the item is substituted and normalized,
  therefore monomorphizing the item. That's how Charon can support monomorphization that's
  guaranteed to give the same results as rustc;
- Synthetic items: items in hax are identified by their `hax::DefId`. For the most part this is just
  a rustc `DefId`, but we also add a couple fictitious items, see `synthetic_items.rs`. These are
  used to simplify the generation of e.g. a concrete `impl<A, B> Fn<(A,)> for fn(A) -> B` item by
  Charon.

The rest is careful use of rustc internal APIs to avoid ICEs and find all the information scattered
throughout the compiler.
