use clap::StructOpt;
/// The options received as input by cargo-charon
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

// This structure is used to store the command-line instructions.
// We automatically derive a command-line parser based on this structure.
// Note that the doc comments are used to generate the help message when using
// `--help`.
//
// Note that because we need to transmit the options to the charon driver,
// we store them in a file before calling this driver (hence the `Serialize`,
// `Deserialize` options).
#[derive(StructOpt, Default, Serialize, Deserialize)]
#[structopt(name = "Charon")]
pub struct CliOpts {
    /// Extract the unstructured LLBC (i.e., don't reconstruct the control-flow)
    #[structopt(long = "ullbc")]
    pub ullbc: bool,
    /// Compile the package's library
    #[structopt(long = "lib")]
    pub lib: bool,
    /// Compile the specified binary
    #[structopt(long = "bin")]
    pub bin: Option<String>,
    /// Extract the promoted MIR instead of the built MIR
    #[structopt(long = "mir_promoted")]
    pub mir_promoted: bool,
    /// Extract the optimized MIR instead of the built MIR
    #[structopt(long = "mir_optimized")]
    pub mir_optimized: bool,
    /// Provide a custom name for the compiled crate (ignore the name computed
    /// by Cargo)
    #[structopt(long = "crate")]
    pub crate_name: Option<String>,
    /// The input file (the entry point of the crate to extract).
    /// This is needed if you want to define a custom entry point (to only
    /// extract part of a crate for instance).
    #[structopt(long = "input", parse(from_os_str))]
    pub input_file: Option<PathBuf>,
    /// The destination directory, if we don't want to generate the output
    /// .llbc files in the same directory as the input .rs files.
    #[structopt(long = "dest", parse(from_os_str))]
    pub dest_dir: Option<PathBuf>,
    /// If activated, use Polonius' non-lexical lifetimes (NLL) analysis.
    /// Otherwise, use the standard borrow checker.
    #[structopt(long = "polonius")]
    pub use_polonius: bool,
    #[structopt(
        long = "no-code-duplication",
        help = "Check that no code duplication happens during control-flow reconstruction
of the MIR code.

This is only used to make sure the reconstructed code is of good quality.
For instance, if we have the following CFG in MIR:
  ```
  b0: switch x [true -> goto b1; false -> goto b2]
  b1: y := 0; goto b3
  b2: y := 1; goto b3
  b3: return y      
  ```

We want to reconstruct the control-flow as:
  ```
  if x then { y := 0; } else { y := 1 };
  return y;
  ```

But if we don't do this reconstruction correctly, we might duplicate
the code starting at b3:
  ```
  if x then { y := 0; return y; } else { y := 1; return y; }
  ```

When activating this flag, we check that no such things happen.

Also note that it is sometimes not possible to prevent code duplication,
if the original Rust looks like this for instance:
  ```
  match x with
  | E1(y,_) | E2(_,y) => { ... } // Some branches are \"fused\"
  | E3 => { ... }
  ```

The reason is that assignments are introduced when desugaring the pattern
matching, and those assignments are specific to the variant on which we pattern
match (the `E1` branch performs: `y := (x as E1).0`, while the `E2` branch
performs: `y := (x as E2).1`). Producing a better reconstruction is non-trivial.
"
    )]
    pub no_code_duplication: bool,
    /// A list of modules of the extracted crate that we consider as opaque: we
    /// extract only the signature information, without the definition content
    /// (of the functions, types, etc.).
    #[structopt(long = "opaque")]
    pub opaque_modules: Vec<String>,
    /// Do not provide a Rust version argument to Cargo (e.g., `+nightly-2022-01-29`).
    /// This is for Nix: outside of Nix, we use Rustup to call the proper version
    /// of Cargo (and thus need this argument), but within Nix we build and call a very
    /// specific version of Cargo.
    #[structopt(long = "cargo-no-rust-version", env = "CARGO_NO_RUST_VERSION")]
    pub cargo_no_rust_version: bool,
    /// Panic on the first error. This is useful for debugging.
    #[structopt(long = "abort-on-error")]
    pub abort_on_error: bool,
    /// Print the errors as warnings
    #[structopt(
        long = "errors-as-warnings",
        help = "
Report the errors as warnings
"
    )]
    pub errors_as_warnings: bool,
    #[structopt(
        long = "print-ullbc",
        help = "
Print the ULLBC immediately after extraction from MIR.
"
    )]
    pub print_ullbc: bool,
    #[structopt(
        long = "print-built-llbc",
        help = "
Print the LLBC just after we built it (i.e., immediately after loop reconstruction).
"
    )]
    pub print_built_llbc: bool,
    #[structopt(
        long = "print-llbc",
        help = "
Print the final LLBC (after all the cleaning micro-passes).
"
    )]
    pub print_llbc: bool,
}

/// The name of the environment variable we use to save the serialized Cli options
/// when calling charon-driver from cargo-charon.
pub const CHARON_ARGS: &str = "CHARON_ARGS";
