# Translating To/Executing With MiniRust

[`MiniRust`](https://github.com/minirust/minirust) is the semi-official specification for the
runtime semantics of Rust. It's an interpreter for a "condensed version" of Rust, whose execution
determines exactly what the program does and what is/isn't UB.

Charon supports converting its output to MiniRust's input language! Pass `--format=minirust` to
`charon` and you will get a json file that can be deserialized and run by MiniRust. Pass
`--run-with-minirust` to `charon` and it will directly execute the `main` function of the translated
crate using MiniRust.

A Charon function body is already pretty close to MiniRust, by the simple fact that both are based
on MIR. The main difference is likely polymorphism: MiniRust only supports monomorphic code, and
Charon will use its monomorphized translation when translating to MiniRust.

MiniRust also serves as the semantic definition of Charon: if there is doubt about the semantics of
a statement, the translation to MiniRust in `src/minirust.rs` is considered authoritative.
