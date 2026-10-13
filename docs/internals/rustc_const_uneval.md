# rustc_const_uneval

`rustc_const_uneval` is a subcrate of Charon which handles evaluating constants with rustc and reading their values back into structured constants ("unevaluating" them). Like [`rustc_trait_elaboration`](./rustc_trait_elaboration.md), this is meant to be a sort of extension of rustc.

The entry point is `ConstReader::read`, which evaluates a `ConstSource` (a `const` item, a promoted, a global, a type-level constant, a valtree or an already-evaluated value) and reads the result either as a structured `Const` or as raw bytes, depending on the `ReadMode`. This avoid duplicating a lot of tricky code around handling these similar entities.

rustc represents evaluated constants in two ways: 
- [valtrees](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/consts/struct.ValTree.html), which are trees of integers used for type-level constants. We read those directly.
- [allocations](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/interpret/struct.Allocation.html), which occur in MIR bodies and consts. We read them by loading them in a const-eval interpreter and walking the value according to its type.

Pointers are the tricky part of this. A pointer to a whole static, which is typed, is kept as a pointer to that global. Whether allocations without an item become globals or get inlined at each use is controlled by `Config::anon_allocs_as_globals`. Note that inlining allocations means **aliasing information is lost**. Finally, wide pointers are read as a thin pointer to the sized value they were unsized from (e.g. `[T; N]` for a `&[T]`), with an `Unsize` that tells how to recover the wide pointer.

Allocations without an item are untyped: we view them as `MaybeUninit<[u8; N]>`, so a pointer only refers to one as a global if it covers the whole allocation. **This loses aliasing information, see [#1225](https://github.com/AeneasVerif/charon/issues/1225)**.

In raw bytes mode, a value is a list of bytes, each of which is uninitialized, a concrete `u8` byte, or part of a pointer to a given target. This mimics [how MiniRust represents allocations](https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes), except that we do not give a value to provenance-having bytes, since that value is non-deterministic. Instead, provenance is an enum, pointing to one of: a function, a global, a vtable or a `TypeId` (this [mimics rustc](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/interpret/enum.GlobalAlloc.html)).

Values we can't represent are read as `ConstKind::Unsupported`.
