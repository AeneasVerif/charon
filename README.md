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

TODO: table des matières

Charon extracts a rust crate into an easy-to-use format, meant to be used for analysis and
code-generation tools.

It extracts:
- type definitions;
- functions with their (polymorphic) signatures and bodies;
- trait declarations and implementations, already-resolved when relevant;
- constants and statics.

TODO: control flow reconstruction 

The output format is as simple as one could imagine: the serde dump (currently in JSON) of the
[`TranslatedCrate`](https://aeneasverif.github.io/charon/charon_lib/ast/krate/struct.TranslatedCrate.html)
type.

TODO: what can be done with charon

TODO: link to paper

Some rust features are not yet supported, e.g., trait aliases, thread-local variables, `dyn Trait`.
See the full list [here](https://github.com/AeneasVerif/charon/issues/142).

We are **open to contributions**! Please contact us so that we can coordinate
if you are willing to contribute. For this purpose you can join the [Zulip](https://aeneas-verif.zulipchat.com/).

# Installation

Charon is made of two parts:
- the `charon` binary is run on a crate and produces a `.llbc` file;
- the `charon-lib` crate (or for Ocaml, the `charon-ml` library) provides the types and functions
  to read the `.llbc` file and use its contents.

## `charon` binary

### Using `nix`

The `charon` binary can be installed using `nix`: `nix build "github:AeneasVerif/charon"` will
produce a `result` directory with the `charon` binary inside.

### Manual build

Install [`rustup`](https://www.rust-lang.org/tools/install) and run `make build-charon-rust`. This
will call `cargo build` and copy the important binaries to `./bin`.

## `charon-lib` crate

The `charon-lib` crate is a normal crate.

TODO: make it easy to use from github or path, without rustc_driver

## `charon-ml` library

If you also want to build the ML library (in `./charon-ml`), you will need to
install OCaml and the proper dependencies.

We suggest you to follow those [instructions](https://ocaml.org/docs/install.html),
and install OPAM on the way (same instructions).

For Charon-ML, we use **OCaml 4.13.1**: `opam switch create 4.13.1+options`

The dependencies can be installed with the following command:

```
opam install ppx_deriving visitors easy_logging zarith yojson core_unix odoc menhir unionFind
```

You can then run `make build-charon-ml` to build the ML library, or even simply
`make` to build the whole project (Rust and OCaml). Finally, you can run the
tests with `make test`.



# Usage

TODO

You can access the Rust documentation
[online](https://aeneasverif.github.io/charon/charon_lib/index.html).

You can also run `make` to generate the documentation locally.
It will generate a documentation accessible from
[`doc-rust.html`](./doc-rust.html) (for the Rust project) and
[`doc-ml.html`](./doc-ml.html) (for the ML library).

# Stability

Charon is in **alpha stage** at the moment. A few major changes to the API are planned, though we
try to avoid them when we can. See issue #XXX

# Contributing

TODO: link CONTRIBUTING

Alternatively, you can use Nix and do `nix develop` (or use https://direnv.net/ and `direnv allow`)
and all dependencies should be made available.

# Project Overview

- pipeline: MIR -> ULLBC -> LLBC, micro-passes
- explain charon -> charon_driver
how it all fits together

<!-- - `charon`: the Rust implementation. -->
<!-- - `charon-ml`: the ML library. Provides utilities to retrieve and manipulate -->
<!--   the AST in OCaml (deserialization, printing, etc.). -->
<!-- - `tests` and `tests-polonius`: test files directories. `tests-polonius` contains -->
<!--   code which requires the Polonius borrow checker. -->

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

## Usage

To run Charon, you should run the Charon binary from *within* the crate that you
want to compile, as if you wanted to build the crate with `cargo build`. The
Charon executable is located at `bin/charon`.

Charon will build the crate and its dependencies, then extract the AST. Charon
provides various options and flags to tweak its behaviour: you can display a
detailed documentation with `--help`.
In particular, you can print the LLBC generated by Charon with `--print-llbc`.

If there is a `Charon.toml` file at the root of your project, charon will also take options from it.
The file supports the same options at the cli interface, except for the options that relate to
input/output like `--print-llbc`. Example `Charon.toml`:
```toml
[charon]
extract_opaque_bodies = true
[rustc]
flags = ["--cfg", "abc"]
```

**Remark**: because Charon is compiled with Rust nigthly (this is a requirement
to implement a rustc driver), it will build your crate with Rust nightly. You
can find the nightly version pinned for Charon in [`rust-toolchain.template`](rust-toolchain.template).

# Citing charon

TODO

# Name

Charon is, in Greek mythology, an old man carrying the souls of the deceased accross the
Styx, a river separating the world of the living from the world of the dead. In the
present context, Charon allows us to go from the world of Rust programs to the world of
formal verification.
