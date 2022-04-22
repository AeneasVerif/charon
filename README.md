<p><div style="text-align: center">
<img src="static/Charon.jpg"
     alt="Landscape with Charon crossing the Styx" title="Landscape with Charon crossing the Styx"
     style=""/>
<figcaption>
Patinir, E., 1515-1524, <i>Landscape with Charon crossing the Styx</i> [Oil on wood].
Museo del Prado, Madrid.
<a href="https://en.wikipedia.org/wiki/Landscape_with_Charon_Crossing_the_Styx">Source</a>
</figcaption>
</div></p>

# Charon
Charon acts as an interface between the rustc compiler and program verification projects. Its
purpose is to process Rust .rs files and convert them into files easy to handle by program
verifiers. It is implemented as a custom driver for the rustc compiler.

Charon is, in Greek mythology, an old man carrying the souls of the deceased accross the
Styx, a river separating the world of the living from the world of the dead. In the
present context, Charon allows us to go from the world of Rust programs to the world of
formal verification.

We are **open to contributions**! Please contact us so that we can coordinate ourselves,
if you are willing to contribute.

## LLBC
Charon converts MIR code to LLBC (Low-Level Borrow Calculus), which is MIR
but with the following differences:
- control-flow has been reconstructed: LLBC uses a structured control-flow with loops,
  if ... then ... else ..., etc. instead of gotos.
- MIR statements and terminators are merged into a single statement type.
  Followingly, we do not manipulate basic blocks, but only statements.
- calls to arithmetic operations are simplified: we remove the dynamic checks for
  divisions by zero and overflows. The rationale is that in theorem provers, those
  operations either have preconditions, or perform the checks themselves.
- (in progress) we adopt a slightly higher-level view of matches over enumerations.
  Instead of having to read the discriminant then switch over it like here:
  ```
  d = read_discriminant(ls : List<T>);
  switch d {
    0 => { ... }
    1 => { ... }
    _ => panic!(),
  }
  ```
  we do:
  ```
  match (read_discriminant(ls)) {
    Cons => { ... }
    Nil => { ... }
  }
  ```
  Note that we still switch over discriminants: the match is not a high-level
  match like in a functional language (i.e., there are no patterns on the left
  of the `=>`, only constructor identifiers).
  Simply, we do not allow the independent manipulation of discriminants, as it is
  very low level.
- (in progress) we do not allow progressive initialization of datatypes,
  but use aggregated values. Instead of this:
  ```
  (x as Cons).0 = move hd;
  (x as Cons).1 = move tl;
  set_discriminant(x, 0);
  ```
  we do:
  ```
  x = Cons { .0 = (move hd), .1 = (move tl) };
  ```
- (in progress) The constants compiled by rustc are "decompiled" into higher-level
  data. Some constants (like borrows compiled as constants) are not supported yet,
  and will be desugared by introducing temporary variables.

**Remark**: most of the transformations above are applied through micro-passes. Depending on
the need, we could make them optional and control them with flags. If you want
to know more about the details, see `translate` in `src/main.rs`, which applies
the micro-passes one after the other.

**Remark**: if you want to know the full details of LLBC, have a look at: `types.rs`,
`values.rs`, `expressions.rs` and `llbc_ast.rs`.

We also reorder the function and type definitions, so that for instance if a function
`f` calls a function `g`, `f` is defined after `g`, mutually recursive definitions are grouped,
etc.

The extracted AST is serialized in .llbc files (using the JSON format).
We generate one file per extracted crate.

## Project Structure

- `charon`: the implementation.
- `macros`: various macros used in the implementation (Rust requires macros to
  be defined in separate libraries due to technical reasons).
- `tests` and `tests-nll`: test files directories. `tests-nll` contains
  code which requires non-lexical lifetimes (i.e., the Polonius borrow checker).

## Installation & Build

You first need to install [`rustup`](https://www.rust-lang.org/tools/install).

As Charon is set up with cargo, rustup will automatically download and install the proper
packages upon building the project: you just need to run `make` in the top directory.

## Usage

To use Charon, you should first build the project to extract in debug mode: `cargo build`.
The reason is that Charon will look for already compiled external dependencies in
`/target/debug/deps/`.

Then, the simplest is to do: `cd charon && cargo run -- [OPTIONS] FILE`,
where `FILE` is the entry point of the crate to extract (`PROJECT_PATH/src/main.rs`,
for instance).

Charon provides various options and flags to tweak its behaviour: you can display a detailed
documentation with `--help`.
