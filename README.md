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
purpose is to process Rust .rs files into files easy to handle by program verifiers.
It is implemented as a custom driver for the rustc compiler.

Charon is, in Greek mythology, an old man carrying the souls of the deceased accross the
Styx, a river separating the world of the living from the world of the dead. In the
present context, Charon allows us to go from the world of Rust programs to the world of
formal verification.

We do so by converting MIR code to LLBC (Low-Level Borrow Calculus), which is very
close to MIR but with some simplifications and where control-flow has been reconstructed
(LLBC uses a structured control-flow with loops, if ... then .. else, etc. instead
of gotos).

# Structure

- `charon`: the implementation of Charon.
- `macros`: various macros used in the implementation (Rust requires macros to
  be defined in separate libraries due to technical reasons).
- `tests` and `tests-nll`: test files directories. `tests-nll` contains
  code which requires non-lexical lifetimes (i.e., the Polonius borrow checker).

# Build

You can build the project and run the tests by running `make` in the top directory.

# Usage

To use Charon, the simplest is to do: `cd charon && cargo run -- [OPTIONS] FILE`,
where `FILE` is the entry point of the crate to extract (`PROJECT_PATH/main.rs`, for instance).

It is possible to tweak Charon's behaviour: use `--help` to print a detailed documentation.
