# AGENTS.md

Guidance for AI agents working on Charon.

## Working Style

- Charon is written with the following values in mind: correctness, robustness, maintainability, and
  solving people's problems (also, finding joy in clean code and abstractions).
- The codebase is built around carefully-crafted invariants, e.g. how we go from rustc to hax to
  charon for `GenericArgs`, or how mono mode is transparent most of the time.
- Read the surrounding code before editing. Most problems in this repository already have a nearby
  pattern in another translation pass, AST utility, or normalization pass.
- We are the owners of this codebase, we can make deep changes if that's the best way to solve
  a problem.
- Exercise judgment: sometimes the right fix is downstream (e.g. in aeneas) or upstream (e.g. in
  rustc itself); I don't shy from fixing the bugs where they should be fixed (though well-placed
  workarounds are often fine).
- Correctness comes first. We should be very careful when modifying what we got from rustc. Even
  tricky cases should be handled correctly; if in doubt, double-check and add tests.
- Robustness comes second. Charon should be able to emit an llbc file even in the face of many
  errors. Use panics appropriately, when they indicate a broken invariant within Charon. Use errors
  when the invariant is less clear and/or there's high risk of it being broken in practice.
- Maintainability comes third. Prefer small, principled changes over local cleverness. A change that
  introduces a ton of code at once is suspicious; there's often a cleaner way. I'm the sole
  maintainer so any unneeded complexity is a cost I'll have to bear in the future.
- If in doubt, ask, and exercise judgment as a good OSS maintainer would.

## Implementing Translation and Transformations

- Avoid constructing generic arguments manually to avoid getting trait references wrong. Prefer
  obtaining generics from an existing call, type, translated item, or Hax/rustc API.
- Be careful about monomorphized mode: it can break some assumptions such as the fact that a given
  item exists only once. If an approach relies on polymorphic item paths, function names, or
  non-monomorphized generic structure, either make it work in mono deliberately or gate the pass off
  in mono mode.
- Prefer rustc and Hax APIs for item discovery and method resolution. Use `def_path_def_ids`/path
  resolution for named standard items, and Hax `ItemRef`s when the result should flow through normal
  Charon translation.
- Be careful with `ctx.translated`: some bodies stored there may not have gone through later body
  cleanup passes yet. If a pass reads from translated bodies while transformations are fused,
  consider whether it is seeing pre-pass or post-pass state.
- If a pass needs a declaration id, prefer an initializer (`Transform::new(ctx)`) that discovers it
  once and stores it in the transform. Put prerequisites in `should_run`, including option gates and
  whether required declarations were found.
- Keep algorithmic complexity under control: generally avoid iterating over the whole crate or
  a whole body too many times.

## Testing

- Every fix should ideally have a reproducer. The test suite is quite flexible, use it.
- Changes to the generated output are to be double-checked: they can often indicate a bug.
  Well-motivated changes are however totally fine.

## OCaml vs Rust

Charon is a hybrid codebase. A typical feature is mostly on the Rust side. However when the AST
changes, this must be propagated. Use `make generate-ml` to regenerate the generated OCaml files.

## Versioning

Any change to the AST must come with a version bump to make the deserializers emit nice errors. Just
bump the patch version in `Cargo.toml` then run `make test` at the root to propagate the changes.
