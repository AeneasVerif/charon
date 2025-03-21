//! Mutate the compiler [`Config`], like through
//! * release / codegen flags
//! * disabled_mir_passes
//!
//! [`Config`]: https://aeneasverif.github.io/charon/rustc/rustc_interface/interface/struct.Config.html

use rustc_interface::Config;
use rustc_session::config::{OutputType, OutputTypes};

/// Disable all these mir passes.
pub fn disabled_mir_passes(config: &mut Config) {
    let disabled_mir_passes = [
        "AfterConstProp",
        "AfterGVN",
        "AfterUnreachableEnumBranching)",
        "BeforeConstProp",
        "CheckAlignment",
        "CopyProp",
        "CriticalCallEdges",
        "DataflowConstProp",
        "DeduplicateBlocks",
        "DestinationPropagation",
        "EarlyOtherwiseBranch",
        "EnumSizeOpt",
        "GVN",
        "Initial",
        "Inline",
        "InstSimplify",
        "JumpThreading",
        "LowerSliceLenCalls",
        "MatchBranchSimplification",
        "MentionedItems",
        "MultipleReturnTerminators",
        "ReferencePropagation",
        "RemoveNoopLandingPads",
        "RemoveStorageMarkers",
        "RemoveUnneededDrops",
        "RemoveZsts",
        "RenameReturnPlace",
        "ReorderBasicBlocks",
        "ReorderLocals",
        "ScalarReplacementOfAggregates",
        "SimplifyComparisonIntegral",
        "SimplifyLocals",
        "SingleUseConsts",
        "UnreachableEnumBranching",
        "UnreachablePropagation",
    ];
    for pass in disabled_mir_passes {
        config
            .opts
            .unstable_opts
            .mir_enable_passes
            .push((pass.to_owned(), false));
    }
}

/// Don't even try to codegen. This avoids errors due to checking if the output filename is
/// available (despite the fact that we won't emit it because we stop compilation early).
pub fn no_codegen(config: &mut Config) {
    config.opts.unstable_opts.no_codegen = true;

    // i.e. --emit=metadata
    let opt_output_types = &mut config.opts.output_types;
    let mut out_types = vec![];
    out_types.extend(opt_output_types.iter().map(|(&k, v)| (k, v.clone())));
    out_types.push((OutputType::Metadata, None));
    *opt_output_types = OutputTypes::new(&out_types);
}

/// Always compile in release mode: in effect, we want to analyze the released
/// code. Also, rustc inserts a lot of dynamic checks in debug mode, that we
/// have to clean. Full list of `--release` flags:
/// https://doc.rust-lang.org/cargo/reference/profiles.html#release
pub fn release_mode(config: &mut Config) {
    let cg = &mut config.opts.cg;
    cg.opt_level = "3".into();
    cg.overflow_checks = Some(false);
    config.opts.debug_assertions = false;
}
