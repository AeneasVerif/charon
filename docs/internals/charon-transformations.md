# Charon transformations

Running `charon` is split into two phases: [*translation*](./charon-translation.md) calls into rustc APIs and constructs
Charon's representation for the crate and its contents,
and *transformations* then transforms the pure-Charon AST 
into its final shape.

See `charon-driver/transform/mod.rs` for a list of passes.
