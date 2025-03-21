//! Run the rustc compiler with our custom options and hooks.
use crate::translate::translate_crate_to_ullbc;
use crate::{arg_values, CharonFailure};
use charon_lib::options::CliOpts;
use charon_lib::transform::TransformCtx;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::Config;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::util::Providers;
use rustc_session::config::{OutputType, OutputTypes, Polonius};
use std::sync::atomic::{AtomicBool, Ordering};
use std::{env, fmt};

/// Helper that runs the compiler and catches its fatal errors.
fn run_compiler_with_callbacks(
    args: Vec<String>,
    callbacks: &mut (dyn Callbacks + Send),
) -> Result<(), CharonFailure> {
    rustc_driver::catch_fatal_errors(|| rustc_driver::RunCompiler::new(&args, callbacks).run())
        .map_err(|_| CharonFailure::RustcError)?
        .map_err(|_| CharonFailure::RustcError)?;
    Ok(())
}

/// Disable all the mir passes we can disable without causing ICEs.
fn disable_mir_opt_passes(config: &mut Config) {
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
fn set_no_codegen(config: &mut Config) {
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
fn set_release_mode(config: &mut Config) {
    let cg = &mut config.opts.cg;
    cg.opt_level = "3".into();
    cg.overflow_checks = Some(false);
    config.opts.debug_assertions = false;
}

// We use a static to be able to pass data to `override_queries`.
static SKIP_BORROWCK: AtomicBool = AtomicBool::new(false);
fn set_skip_borrowck() {
    SKIP_BORROWCK.store(true, Ordering::SeqCst);
}
fn skip_borrowck_if_set(providers: &mut Providers) {
    if SKIP_BORROWCK.load(Ordering::SeqCst) {
        providers.mir_borrowck = |tcx, def_id| {
            let (input_body, _promoted) = tcx.mir_promoted(def_id);
            let input_body = &input_body.borrow();
            // Empty result, which is what is used for tainted or custom_mir bodies.
            let result = rustc_middle::mir::BorrowCheckResult {
                concrete_opaque_types: Default::default(),
                closure_requirements: None,
                used_mut_upvars: Default::default(),
                tainted_by_errors: input_body.tainted_by_errors,
            };
            tcx.arena.alloc(result)
        }
    }
}

fn setup_compiler(config: &mut Config, options: &CliOpts, do_translate: bool) {
    if do_translate {
        if options.skip_borrowck {
            // We use a static to be able to pass data to `override_queries`.
            set_skip_borrowck();
        }

        config.override_queries = Some(|_sess, providers| {
            skip_borrowck_if_set(providers);

            // TODO: catch the MIR in-flight to avoid stealing issues?
            // providers.mir_built = |tcx, def_id| {
            //     let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
            //     let mut mir = mir.steal();
            //     // use the mir
            //     tcx.alloc_steal_mir(mir)
            // };
        });

        disable_mir_opt_passes(config);
        set_release_mode(config);
        set_no_codegen(config);
    }
    if options.use_polonius {
        config.opts.unstable_opts.polonius = Polonius::Legacy;
    }
}

/// Run the rustc driver with our custom hooks. Returns `None` if the crate was not compiled with
/// charon (e.g. because it was a dependency). Otherwise returns the translated crate, ready for
/// post-processing transformations.
pub fn run_rustc_driver(options: &CliOpts) -> Result<Option<TransformCtx>, CharonFailure> {
    // Retreive the command-line arguments pased to `charon_driver`. The first arg is the path to
    // the current executable, we skip it.
    let mut compiler_args: Vec<String> = env::args().skip(1).collect();

    // Cargo calls the driver twice. The first call to the driver is with "--crate-name ___" and no
    // source file, for Cargo to retrieve some information about the crate.
    let is_dry_run = arg_values(&compiler_args, "--crate-name")
        .find(|s| *s == "___")
        .is_some();
    // When called using cargo, we tell cargo to use `charon-driver` by setting the
    // `RUSTC_WORKSPACE_WRAPPER` env var. This uses `charon-driver` for all the crates in the
    // workspace. We may however not want to be calling charon on all crates;
    // `CARGO_PRIMARY_PACKAGE` tells us whether the crate was specifically selected or is a
    // dependency.
    let is_workspace_dependency =
        env::var("CHARON_USING_CARGO").is_ok() && !env::var("CARGO_PRIMARY_PACKAGE").is_ok();
    // Determines if we are being invoked to build a crate for the "target" architecture, in
    // contrast to the "host" architecture. Host crates are for build scripts and proc macros and
    // still need to be built like normal; target crates need to be processed by Charon.
    //
    // Currently, we detect this by checking for "--target=", which is never set for host crates.
    // This matches what Miri does, which hopefully makes it reliable enough. This relies on us
    // always invoking cargo itself with `--target`, which `charon` ensures.
    let is_target = arg_values(&compiler_args, "--target").next().is_some();

    let no_translate = is_dry_run || is_workspace_dependency || !is_target;
    let output = if no_translate {
        trace!("Skipping charon; running compiler normally instead.");
        // Run the compiler normally.
        run_compiler_with_callbacks(compiler_args, &mut RunCompilerNormallyCallbacks { options })?;
        None
    } else {
        for extra_flag in options.rustc_args.iter().cloned() {
            compiler_args.push(extra_flag);
        }

        // Call the Rust compiler with our custom callback.
        let mut callback = CharonCallbacks {
            options,
            transform_ctx: None,
        };
        run_compiler_with_callbacks(compiler_args, &mut callback)?;
        // If `transform_ctx` is not set here, there was a fatal error.
        let ctx = callback.transform_ctx.ok_or(CharonFailure::RustcError)?;
        Some(ctx)
    };
    Ok(output)
}

/// Custom `DefId` debug routine that doesn't print unstable values like ids and hashes.
fn def_id_debug(def_id: rustc_hir::def_id::DefId, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    rustc_middle::ty::tls::with_opt(|opt_tcx| {
        if let Some(tcx) = opt_tcx {
            let crate_name = if def_id.is_local() {
                tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE)
            } else {
                tcx.cstore_untracked().crate_name(def_id.krate)
            };
            write!(
                f,
                "{}{}",
                crate_name,
                tcx.def_path(def_id).to_string_no_crate_verbose()
            )?;
        } else {
            write!(f, "<can't access `tcx` to print `DefId` path>")?;
        }
        Ok(())
    })
}

/// The callbacks for Charon
pub struct CharonCallbacks<'a> {
    pub options: &'a CliOpts,
    /// This is to be filled during the extraction; it contains the translated crate.
    transform_ctx: Option<TransformCtx>,
}
impl<'a> Callbacks for CharonCallbacks<'a> {
    fn config(&mut self, config: &mut Config) {
        setup_compiler(config, self.options, true);
    }

    /// The MIR is modified in place: borrow-checking requires the "promoted" MIR, which causes the
    /// "built" MIR (which results from the conversion to HIR to MIR) to become unaccessible.
    /// Because we require built MIR at the moment, we hook ourselves before MIR-based analysis
    /// passes.
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // Set up our own `DefId` debug routine.
        rustc_hir::def_id::DEF_ID_DEBUG
            .swap(&(def_id_debug as fn(_, &mut fmt::Formatter<'_>) -> _));

        let transform_ctx = queries.global_ctxt().unwrap().get_mut().enter(|tcx| {
            translate_crate_to_ullbc::translate(&self.options, tcx, compiler.sess.sysroot.clone())
        });
        self.transform_ctx = Some(transform_ctx);
        Compilation::Continue
    }
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        _: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // Don't continue to codegen etc.
        Compilation::Stop
    }
}

/// Dummy callbacks used to run the compiler normally when we shouldn't be analyzing the crate.
pub struct RunCompilerNormallyCallbacks<'a> {
    options: &'a CliOpts,
}
impl<'a> Callbacks for RunCompilerNormallyCallbacks<'a> {
    fn config(&mut self, config: &mut Config) {
        setup_compiler(config, self.options, false);
    }
}
