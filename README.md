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
- we desugar a bit accesses to constants and globals. In MIR, constants and globals
  can be accessed in operands, while in LLBC we introduce intermediate assignments
  so that they are accessed only by means of an `AssignGlobal` statement (which
  reads a global and stores it in a local variable).

**Remark**: most of the transformations above are applied through micro-passes. Depending on
the need, we could make them optional and control them with flags. If you want
to know more about the details, see `translate` in `src/main.rs`, which applies
the micro-passes one after the other.

**Remark**: if you want to know the full details of LLBC, have a look at: `types.rs`,
`values.rs`, `expressions.rs` and `llbc_ast.rs`.

We also reorder the function and type definitions, so that for instance if a
function `f` calls a function `g`, `f` is defined after `g`, mutually recursive
definitions are grouped, etc.

The extracted AST is serialized in .llbc files (using the JSON format).
We generate one file per extracted crate.

## Project Structure

- `charon`: the implementation.
- `macros`: various macros used in the implementation (Rust requires macros to
  be defined in separate libraries due to technical reasons).
- `tests` and `tests-polonius`: test files directories. `tests-polonius` contains
  code which requires non-lexical lifetimes (i.e., the Polonius borrow checker).

## Installation & Build

You first need to install [`rustup`](https://www.rust-lang.org/tools/install).

As Charon is set up with cargo, rustup will automatically download and install the proper
packages upon building the project. If you only want to build the Rust project (in
`./charon`), simply run `make build-charon-rust` in the top directory.

If you also want to build the ML library (in `./charon-ml`), you will need to
install OCaml and the proper dependencies.

We suggest you to follow those [instructions](https://ocaml.org/docs/install.html),
and install OPAM on the way (same instructions).

We use **OCaml 4.13.1**: `opam switch create 4.13.1+options`

The dependencies can then be installed with the following command:

```
opam install ppx_deriving visitors easy_logging zarith yojson core_unix odoc
```

You can then run `make build-charon-ml` to build the ML library, or even simply
`make` to build the whole project and run the tests.

## Documentation

If you run `make`, you will generate a documentation accessible from
[`doc-rust.html`](./doc-rust.html) (for the Rust project) and
[`doc-ml.html`](./doc-ml.html) (for the ML library).

## Usage

To use Charon, you should first build the project you wish to extract in debug mode: `cargo build`.
The reason is that Charon will look for already compiled external dependencies in the
target directory (`/target/debug/deps/`, usually).

Then, the simplest is to do: `cd charon && cargo run -- [OPTIONS] FILE`,
where `FILE` is the entry point of the crate to extract (`PROJECT_PATH/src/main.rs`,
for instance).

**Remark**: the crate to be extracted must be built with the same version of rustc
as Charon (see the file `charon/rust-toolchain`). If it is not the case, the extraction
will likely fail with an error saying that there is a mismatch in the metadata of the compiled
files.

Charon provides various options and flags to tweak its behaviour: you can display a detailed
documentation with `--help`.
