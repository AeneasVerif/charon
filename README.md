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
purpose is to process Rust crates and convert them into files easy to handle by program
verifiers. It is implemented as a custom driver for the rustc compiler.

Charon is, in Greek mythology, an old man carrying the souls of the deceased accross the
Styx, a river separating the world of the living from the world of the dead. In the
present context, Charon allows us to go from the world of Rust programs to the world of
formal verification.

We are **open to contributions**! Please contact us so that we can coordinate ourselves,
if you are willing to contribute. For this purpose you can join the [Zulip](https://aeneas-verif.zulipchat.com/).

## LLBC
Charon converts MIR code to ULLBC (Unstructured Low-Level Borrow Calculus) then
to LLBC. Both ASTs can be output by Charon.

ULLBC is a slightly simplified MIR, where we try to remove as much redundancies
as possible. For instance, we drastically simplify the representation of constants coming
from the Rust compiler.

LLBC is ULLBC where we restructured the control-flow with loops, `if
... then ... else ...`, etc. instead of gotos. Consequently, we merge MIR
statements and terminators into a single LLBC statement type. We also perform
some additional modifications, some of which are listed below:

**Remark**: most of the transformations which transform the MIR to ULLBC then LLBC are
implemented by means of micro-passes. Depending on the need, we could make them optional
and control them with flags. If you want to know more about the details, see `translate`
in `src/driver.rs`, which applies the micro-passes one after the other.

**Remark**: if you want to know the full details of (U)LLBC, have a look at: `types.rs`,
`values.rs`, `expressions.rs`, `ullbc_ast.rs` and `llbc_ast.rs`.

The extracted AST is serialized in `.ullbc` and `.llbc` files (using the JSON format).
We extract a whole crate in one file.

## Project Structure

- `charon`: the Rust implementation.
- `charon-ml`: the ML library. Provides utilities to retrieve and manipulate
  the AST in OCaml (deserialization, printing, etc.).
- `tests` and `tests-polonius`: test files directories. `tests-polonius` contains
  code which requires the Polonius borrow checker.

## Installation & Build

You first need to install [`rustup`](https://www.rust-lang.org/tools/install).

As Charon is set up with cargo, rustup will automatically download and install the proper
packages upon building the project. If you only want to build the Rust project (in
`./charon`), simply run `make build-charon-rust` in the top directory.

If you also want to build the ML library (in `./charon-ml`), you will need to
install OCaml and the proper dependencies.

We suggest you to follow those [instructions](https://ocaml.org/docs/install.html),
and install OPAM on the way (same instructions).

For Charon-ML, we use **OCaml 4.13.1**: `opam switch create 4.13.1+options`

The dependencies can be installed with the following command:

```
opam install ppx_deriving visitors easy_logging zarith yojson core_unix odoc menhir
```

You can then run `make build-charon-ml` to build the ML library, or even simply
`make` to build the whole project (Rust and OCaml). Finally, you can run the
tests with `make test`.

## Documentation

If you run `make`, you will generate a documentation accessible from
[`doc-rust.html`](./doc-rust.html) (for the Rust project) and
[`doc-ml.html`](./doc-ml.html) (for the ML library).

## Usage

To run Charon, you should run the Charon binary from *within* the crate that you
want to compile, as if you wanted to build the crate with `cargo build`. The
Charon executable is located at `bin/charon`.

Charon will build the crate and its dependencies, then extract the AST. Charon
provides various options and flags to tweak its behaviour: you can display a
detailed documentation with `--help`.
In particular, you can print the LLBC generated by Charon with `--print-llbc`.

**Remark**: because Charon is compiled with Rust nigthly (this is a requirement
to implement a rustc driver), it will build your crate with Rust nightly. You
can find the nightly version pinned for Charon in [`rust-toolchain.template`](rust-toolchain.template).
