//! The options that control charon behavior.
use clap::Parser;
use indoc::indoc;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::{ast::*, errors::ErrorCtx, name_matcher::NamePattern, raise_error, register_error};

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
    /// Read an llbc file and pretty-print it. This is a terrible API, we should use subcommands.
    #[clap(long = "read-llbc", value_parser)]
    #[serde(default)]
    pub read_llbc: Option<PathBuf>,
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
    /// If activated, this skips borrow-checking of the crate.
    #[clap(long = "skip-borrowck")]
    #[serde(default)]
    pub skip_borrowck: bool,
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
    /// Monomorphize the code, replacing generics with their concrete types.
    #[clap(long = "monomorphize")]
    #[serde(default)]
    pub monomorphize: bool,
    /// Usually we skip the bodies of foreign methods and structs with private fields. When this
    /// flag is on, we don't.
    #[clap(long = "extract-opaque-bodies")]
    #[serde(default)]
    pub extract_opaque_bodies: bool,
    /// Usually we skip the provided methods that aren't used. When this flag is on, we translate
    /// them all.
    #[clap(long = "translate-all-methods")]
    #[serde(default)]
    pub translate_all_methods: bool,
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
    /// Do nothing! Just run cargo, don't do any translation.
    #[clap(long = "only-cargo")]
    #[serde(default)]
    pub only_cargo: bool,
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

/// TODO: maybe we should always target MIR Built, this would make things
/// simpler. In particular, the MIR optimized is very low level and
/// reveals too many types and data-structures that we don't want to manipulate.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MirLevel {
    /// Original MIR, directly translated from HIR.
    Built,
    /// Not sure what this is. Not well tested.
    Promoted,
    /// MIR after optimization passes. The last one before codegen.
    Optimized,
}

/// The options that control translation and transformation.
pub struct TranslateOptions {
    /// The level at which to extract the MIR
    pub mir_level: MirLevel,
    /// Usually we skip the provided methods that aren't used. When this flag is on, we translate
    /// them all.
    pub translate_all_methods: bool,
    /// Error out if some code ends up being duplicated by the control-flow
    /// reconstruction (note that because several patterns in a match may lead
    /// to the same branch, it is node always possible not to duplicate code).
    pub no_code_duplication: bool,
    /// Whether to hide the `Sized`, `Sync`, `Send` and `Unpin` marker traits anywhere they show
    /// up.
    pub hide_marker_traits: bool,
    /// Monomorphize functions.
    pub monomorphize: bool,
    /// Do not merge the chains of gotos.
    pub no_merge_goto_chains: bool,
    /// Print the llbc just after control-flow reconstruction.
    pub print_built_llbc: bool,
    /// List of patterns to assign a given opacity to. Same as the corresponding `TranslateOptions`
    /// field.
    pub item_opacities: Vec<(NamePattern, ItemOpacity)>,
    /// List of traits for which we transform associated types to type parameters.
    pub remove_associated_types: Vec<NamePattern>,
}

impl TranslateOptions {
    pub fn new(error_ctx: &mut ErrorCtx, options: &CliOpts) -> Self {
        let mut parse_pattern = |s: &str| match NamePattern::parse(s) {
            Ok(p) => Ok(p),
            Err(e) => {
                raise_error!(
                    error_ctx,
                    crate(&TranslatedCrate::default()),
                    Span::dummy(),
                    "failed to parse pattern `{s}` ({e})"
                )
            }
        };

        let mir_level = if options.mir_optimized {
            MirLevel::Optimized
        } else if options.mir_promoted {
            MirLevel::Promoted
        } else {
            MirLevel::Built
        };

        let item_opacities = {
            use ItemOpacity::*;
            let mut opacities = vec![];

            // This is how to treat items that don't match any other pattern.
            if options.extract_opaque_bodies {
                opacities.push(("_".to_string(), Transparent));
            } else {
                opacities.push(("_".to_string(), Foreign));
            }

            // We always include the items from the crate.
            opacities.push(("crate".to_owned(), Transparent));

            for pat in options.include.iter() {
                opacities.push((pat.to_string(), Transparent));
            }
            for pat in options.opaque.iter() {
                opacities.push((pat.to_string(), Opaque));
            }
            for pat in options.exclude.iter() {
                opacities.push((pat.to_string(), Invisible));
            }

            // We always hide this trait.
            opacities.push((format!("core::alloc::Allocator"), Invisible));
            opacities.push((
                format!("alloc::alloc::{{impl core::alloc::Allocator for _}}"),
                Invisible,
            ));

            opacities
                .into_iter()
                .filter_map(|(s, opacity)| parse_pattern(&s).ok().map(|pat| (pat, opacity)))
                .collect()
        };

        let remove_associated_types = options
            .remove_associated_types
            .iter()
            .filter_map(|s| parse_pattern(&s).ok())
            .collect();

        TranslateOptions {
            mir_level,
            no_code_duplication: options.no_code_duplication,
            hide_marker_traits: options.hide_marker_traits,
            monomorphize: options.monomorphize,
            no_merge_goto_chains: options.no_merge_goto_chains,
            print_built_llbc: options.print_built_llbc,
            item_opacities,
            remove_associated_types,
            translate_all_methods: options.translate_all_methods,
        }
    }

    /// Find the opacity requested for the given name. This does not take into account
    /// `#[charon::opaque]` annotations, only cli parameters.
    pub fn opacity_for_name(&self, krate: &TranslatedCrate, name: &Name) -> ItemOpacity {
        // Find the most precise pattern that matches this name. There is always one since
        // the list contains the `_` pattern. If there are conflicting settings for this item, we
        // err on the side of being more opaque.
        let (_, opacity) = self
            .item_opacities
            .iter()
            .filter(|(pat, _)| pat.matches(krate, name))
            .max()
            .unwrap();
        *opacity
    }
}
