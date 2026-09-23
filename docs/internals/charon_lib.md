# charon_lib

`charon_lib` contains the full AST that Charon uses to represent a crate and its contents, along
with (de)serialization logic, [transformations](./charon-transformations.md), and all sorts of
helpers.

Unlike the [translation](./charon-translation.md) machinery that uses rustc internal APIs and
therefore only works on nightly,
this crate is a plain old Rust crate that compiles on stable (you just have to pass
`--no-default-features` to `cargo`).
