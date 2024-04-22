use clap::Parser;
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
#[derive(Debug, Default, Clone, Parser, Serialize, Deserialize)]
#[clap(name = "Charon")]
pub struct CliOpts {
    /// Extract the unstructured LLBC (i.e., don't reconstruct the control-flow)
    #[clap(long = "ullbc")]
    #[serde(default)]
    pub ullbc: bool,
    /// Compile the package's library
    #[clap(long = "lib")]
    #[serde(default)]
    pub lib: bool,
    /// Compile the specified binary
    #[clap(long = "bin")]
    #[serde(default)]
    pub bin: Option<String>,
    /// Extract the promoted MIR instead of the built MIR
    #[clap(long = "mir_promoted")]
    #[serde(default)]
    pub mir_promoted: bool,
    /// Extract the optimized MIR instead of the built MIR
    #[clap(long = "mir_optimized")]
    #[serde(default)]
    pub mir_optimized: bool,
    /// Provide a custom name for the compiled crate (ignore the name computed
    /// by Cargo)
    #[clap(long = "crate")]
    #[serde(default)]
    pub crate_name: Option<String>,
    /// The input file (the entry point of the crate to extract).
    /// This is needed if you want to define a custom entry point (to only
    /// extract part of a crate for instance).
    #[clap(long = "input", parse(from_os_str))]
    #[serde(default)]
    pub input_file: Option<PathBuf>,
    /// The destination directory. Files will be generated as `<dest_dir>/<crate_name>.{u}llbc`,
    /// unless `dest_file` is set. `dest_dir` defaults to the current directory.
    #[clap(long = "dest", parse(from_os_str))]
    #[serde(default)]
    pub dest_dir: Option<PathBuf>,
    /// The destination file. By default `<dest_dir>/<crate_name>.llbc`. If this is set we ignore
    /// `dest_dir`.
    #[clap(long = "dest-file", parse(from_os_str))]
    #[serde(default)]
    pub dest_file: Option<PathBuf>,
    /// If activated, use Polonius' non-lexical lifetimes (NLL) analysis.
    /// Otherwise, use the standard borrow checker.
    #[clap(long = "polonius")]
    #[serde(default)]
    pub use_polonius: bool,
    #[clap(
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
    #[serde(default)]
    pub no_code_duplication: bool,
    /// A list of modules of the extracted crate that we consider as opaque: we
    /// extract only the signature information, without the definition content
    /// (of the functions, types, etc.).
    #[clap(long = "opaque")]
    #[serde(default)]
    pub opaque_modules: Vec<String>,
    /// Usually we skip the bodies of foreign methods and structs with private fields. When this
    /// flag is on, we don't.
    #[clap(long = "extract-opaque-bodies")]
    #[serde(default)]
    pub extract_opaque_bodies: bool,
    /// Do not run cargo; instead, run the driver directly.
    // FIXME: use a subcommand instead, when we update clap to support flattening.
    #[clap(long = "no-cargo")]
    #[serde(default)]
    pub no_cargo: bool,
    /// Panic on the first error. This is useful for debugging.
    #[clap(long = "abort-on-error")]
    #[serde(default)]
    pub abort_on_error: bool,
    /// Print the errors as warnings
    #[clap(
        long = "errors-as-warnings",
        help = "
Report the errors as warnings
"
    )]
    #[serde(default)]
    pub errors_as_warnings: bool,
    #[clap(
        long = "no-serialize",
        help = "
Don't serialize the final (U)LLBC to a file.
"
    )]
    #[serde(default)]
    pub no_serialize: bool,
    #[clap(
        long = "print-ullbc",
        help = "
Print the ULLBC immediately after extraction from MIR.
"
    )]
    #[serde(default)]
    pub print_ullbc: bool,
    #[clap(
        long = "print-built-llbc",
        help = "
Print the LLBC just after we built it (i.e., immediately after loop reconstruction).
"
    )]
    #[serde(default)]
    pub print_built_llbc: bool,
    #[clap(
        long = "print-llbc",
        help = "
Print the final LLBC (after all the cleaning micro-passes).
"
    )]
    #[serde(default)]
    pub print_llbc: bool,
}

/// The name of the environment variable we use to save the serialized Cli options
/// when calling charon-driver from cargo-charon.
pub const CHARON_ARGS: &str = "CHARON_ARGS";
