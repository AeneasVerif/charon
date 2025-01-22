//! The options received as input by cargo-charon
#![allow(dead_code)]
use clap::Parser;
use indoc::indoc;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// The name of the environment variable we use to save the serialized Cli options
/// when calling charon-driver from cargo-charon.
pub const CHARON_ARGS: &str = "CHARON_ARGS";

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
#[charon::rename("cli_options")]
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
    #[clap(long = "input", value_parser)]
    #[serde(default)]
    pub input_file: Option<PathBuf>,
    /// The destination directory. Files will be generated as `<dest_dir>/<crate_name>.{u}llbc`,
    /// unless `dest_file` is set. `dest_dir` defaults to the current directory.
    #[clap(long = "dest", value_parser)]
    #[serde(default)]
    pub dest_dir: Option<PathBuf>,
    /// The destination file. By default `<dest_dir>/<crate_name>.llbc`. If this is set we ignore
    /// `dest_dir`.
    #[clap(long = "dest-file", value_parser)]
    #[serde(default)]
    pub dest_file: Option<PathBuf>,
    /// If activated, use Polonius' non-lexical lifetimes (NLL) analysis.
    /// Otherwise, use the standard borrow checker.
    #[clap(long = "polonius")]
    #[serde(default)]
    pub use_polonius: bool,
    #[clap(
        long = "no-code-duplication",
        help = indoc!("
            Check that no code duplication happens during control-flow reconstruction
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
    "))]
    #[serde(default)]
    pub no_code_duplication: bool,
    /// Usually we skip the bodies of foreign methods and structs with private fields. When this
    /// flag is on, we don't.
    #[clap(long = "extract-opaque-bodies")]
    #[serde(default)]
    pub extract_opaque_bodies: bool,
    /// Whitelist of items to translate. These use the name-matcher syntax.
    #[clap(
        long = "include",
        help = indoc!("
            Whitelist of items to translate. These use the name-matcher syntax (note: this differs
            a bit from the ocaml NameMatcher).

            Note: This is very rough at the moment. E.g. this parses `u64` as a path instead of the
            built-in type. It is also not possible to filter a trait impl (this will only filter
            its methods). Please report bugs or missing features.

            Examples:
              - `crate::module1::module2::item`: refers to this item and all its subitems (e.g.
                  submodules or trait methods);
              - `crate::module1::module2::item::_`: refers only to the subitems of this item;
              - `core::convert::{impl core::convert::Into<_> for _}`: retrieve the body of this
                  very useful impl;

            When multiple patterns in the `--include` and `--opaque` options match the same item,
            the most precise pattern wins. E.g.: `charon --opaque crate::module --include
            crate::module::_` makes the `module` opaque (we won't explore its contents), but the
            items in it transparent (we will translate them if we encounter them.)
    "))]
    #[serde(default)]
    #[charon::rename("included")]
    pub include: Vec<String>,
    /// Blacklist of items to keep opaque. These use the name-matcher syntax.
    #[clap(
        long = "opaque",
        help = "Blacklist of items to keep opaque. Works just like `--include`, see the doc there."
    )]
    #[serde(default)]
    pub opaque: Vec<String>,
    /// Blacklist of items to not translate at all. These use the name-matcher syntax.
    #[clap(
        long = "exclude",
        help = "Blacklist of items to not translate at all. Works just like `--include`, see the doc there."
    )]
    #[serde(default)]
    pub exclude: Vec<String>,
    /// List of traits for which we transform associated types to type parameters.
    #[clap(
        long = "remove-associated-types",
        help = "List of traits for which we transform associated types to type parameters. \
        The syntax is like `--include`, see the doc there."
    )]
    #[serde(default)]
    pub remove_associated_types: Vec<String>,
    /// Whether to hide the `Sized`, `Sync`, `Send` and `Unpin` marker traits anywhere they show
    /// up.
    #[clap(long = "hide-marker-traits")]
    #[serde(default)]
    pub hide_marker_traits: bool,
    /// Do not run cargo; instead, run the driver directly.
    // FIXME: use a subcommand instead, when we update clap to support flattening.
    #[clap(long = "no-cargo")]
    #[serde(default)]
    pub no_cargo: bool,
    /// Extra flags to pass to rustc.
    #[clap(long = "rustc-flag", alias = "rustc-arg")]
    #[serde(default)]
    pub rustc_args: Vec<String>,
    /// Extra flags to pass to cargo. Incompatible with `--no-cargo`.
    #[clap(long = "cargo-arg")]
    #[serde(default)]
    pub cargo_args: Vec<String>,
    /// Panic on the first error. This is useful for debugging.
    #[clap(long = "abort-on-error")]
    #[serde(default)]
    pub abort_on_error: bool,
    /// Print the errors as warnings
    #[clap(long = "error-on-warnings", help = "Consider any warnings as errors")]
    #[serde(default)]
    pub error_on_warnings: bool,
    #[clap(
        long = "no-serialize",
        help = "Don't serialize the final (U)LLBC to a file."
    )]
    #[serde(default)]
    pub no_serialize: bool,
    #[clap(
        long = "print-original-ullbc",
        help = "Print the ULLBC immediately after extraction from MIR."
    )]
    #[serde(default)]
    pub print_original_ullbc: bool,
    #[clap(
        long = "print-ullbc",
        help = "Print the ULLBC after applying the micro-passes (before serialization/control-flow reconstruction)."
    )]
    #[serde(default)]
    pub print_ullbc: bool,
    #[clap(
        long = "print-built-llbc",
        help = "Print the LLBC just after we built it (i.e., immediately after loop reconstruction)."
    )]
    #[serde(default)]
    pub print_built_llbc: bool,
    #[clap(
        long = "print-llbc",
        help = "Print the final LLBC (after all the cleaning micro-passes)."
    )]
    #[serde(default)]
    pub print_llbc: bool,
    #[clap(
        long = "no-merge-goto-chains",
        help = indoc!("
            Do not merge the chains of gotos in the ULLBC control-flow graph.
    "))]
    #[serde(default)]
    pub no_merge_goto_chains: bool,
}

impl CliOpts {
    /// Check that the options are meaningful
    pub fn validate(&self) {
        assert!(
            !self.lib || self.bin.is_none(),
            "Can't use --lib and --bin at the same time"
        );

        assert!(
            !self.mir_promoted || !self.mir_optimized,
            "Can't use --mir_promoted and --mir_optimized at the same time"
        );
    }
}
