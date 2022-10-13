/// The options received as input by cargo-charon
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use structopt::StructOpt;

// This structure is used to store the command-line instructions.
// We automatically derive a command-line parser based on this structure.
// Note that the doc comments are used to generate the help message when using
// `--help`.
//
// TODO: give the possibility of changing the crate name.
//
// Note that because we need to transmit the options to the charon driver,
// we store them in a file before calling this driver (hence the `Serialize`,
// `Deserialize` options).
#[derive(StructOpt, Serialize, Deserialize)]
#[structopt(name = "Charon")]
pub struct CliOpts {
    /// Compile for release target instead of debug
    #[structopt(long = "release")]
    pub release: bool,
    /// The input file (the entry point of the crate to extract)
    #[structopt(parse(from_os_str))]
    pub input_file: PathBuf,
    /// The destination directory, if we don't want to generate the output
    /// .llbc files in the same directory as the input .rs files.
    #[structopt(long = "dest", parse(from_os_str))]
    pub dest_dir: Option<PathBuf>,
    /// If activated, use Polonius' non-lexical lifetimes (NLL) analysis.
    /// Otherwise, use the standard borrow checker.
    #[structopt(long = "nll")]
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
    pub opaque: Vec<String>,
}

/// The name of the environment variable we use to save the serialized Cli options
/// when calling charon-driver from cargo-charon.
pub const CHARON_ARGS: &'static str = "CHARON_ARGS";
