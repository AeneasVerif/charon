# Structured vs Unstructured Control-Flow

Charon can represent a function body in two ways. Both describe the same computation; they differ in
how they connect one operation to the next.

**Structured control-flow** is the default. In this mode, control-flow is represented by having
[`Statement`][structured-statement]s
be able to contain [`Block`][structured-block]s
(statement lists),
e.g. a [`match`][structured-switch]
will contain one block
for each possible branch, and a [function call][structured-call]
will contain a block for its unwind path. The only
"indirect" control-flow affordances are `break`/`continue` within a loop.

**Unstructured control-flow** instead represents the function body as a set of blocks that can jump
to one another. Each [`Block`][unstructured-block] contains a series of control-flow-free
[`Statement`][unstructured-statement]s,
followed by a single
[`Terminator`][unstructured-terminator],
which describes which other blocks computation may jump to.
For example,
a [`match`][unstructured-switch]
will contain one block id
for each possible branch.
Loops are not explicitly represented: they are simply cases where the graph of blocks is cyclic.

Pass `--ullbc` to get unstructured bodies in the output.

The unstructured bodies are actually what `rustc` gives us;
we [reconstruct the structured bodies][reconstruction] ourselves.

### Code Duplication

In structured mode, by default we aim for the output code to be legible, and for that we may
duplicate input code. For example:

```rust
if foo() && bar() {
    do_something();
} else {
    do_something_else();
}
```
is today reconstructed as:
```rust
if foo() {
    if bar() {
        do_something();
    } else {
        do_something_else();
    }
} else {
    do_something_else();
}
```

This specific case may be improved (see [charon#803][charon-803]), but in
the general case we will still have duplication.

If this is undesirable for your use case, use `--no-code-duplication`. Instead of duplicating code
this will introduce `loop`s and `break` from them. Our example becomes more or less:

```rust
'a: loop {
    if foo() {
        if bar() {
            do_something();
            break 'a
        }
    }
    do_something_else();
}
```

[structured-statement]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/structured/struct.Statement.html
[structured-block]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/structured/struct.Block.html
[structured-switch]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/structured/enum.StatementKind.html#variant.Switch
[structured-call]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/structured/enum.StatementKind.html#variant.Call
[unstructured-block]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/unstructured/struct.Block.html
[unstructured-statement]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/unstructured/struct.Statement.html
[unstructured-terminator]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/unstructured/struct.Terminator.html
[unstructured-switch]: https://aeneasverif.github.io/charon/charon_lib/ast/bodies/unstructured/enum.TerminatorKind.html#variant.Switch
[reconstruction]: ../reconstructed-information/control-flow.md
[charon-803]: https://github.com/AeneasVerif/charon/issues/803
