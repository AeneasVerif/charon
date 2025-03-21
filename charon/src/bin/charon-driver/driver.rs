//! Run the rustc compiler with our custom options and hooks.
use crate::translate::translate_crate_to_ullbc;
use crate::{arg_values, CharonFailure};
use charon_lib::options;
use charon_lib::options::CliOpts;
use charon_lib::transform::TransformCtx;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::Config;
use rustc_interface::{interface::Compiler, Queries};
use rustc_session::config::{OutputType, OutputTypes, Polonius};
use std::sync::atomic::{AtomicBool, Ordering};
use std::{env, fmt};

/// Disable all these mir passes.
fn disabled_mir_passes(config: &mut Config) {
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
fn no_codegen(config: &mut Config) {
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
fn release_mode(config: &mut Config) {
    let cg = &mut config.opts.cg;
    cg.opt_level = "3".into();
    cg.overflow_checks = Some(false);
    config.opts.debug_assertions = false;
}

/// -Zpolonius
fn polonius(config: &mut Config, enable: bool) {
    if enable {
        config.opts.unstable_opts.polonius = Polonius::Legacy;
    }
}

pub struct DriverOutput {
    pub options: CliOpts,
    /// The translated crate, ready for post-processing transformations.
    pub ctx: TransformCtx,
}

/// Run the rustc driver with our custom hooks. Returns `None` if the crate was not compiled with
/// charon (e.g. because it was a dependency).
pub fn run_rustc_driver(options: CliOpts) -> Result<Option<DriverOutput>, CharonFailure> {
    // Retreive the command-line arguments pased to `charon_driver`. The first arg is the path to
    // the current executable, we skip it.
    let compiler_args: Vec<String> = env::args().skip(1).collect();

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
    if no_translate {
        trace!("Skipping charon; running compiler normally instead.");
        // In this case we run the compiler normally.
        RunCompilerNormallyCallbacks::new(options)
            .run_compiler(compiler_args)
            .unwrap();
        return Ok(None);
    }

    trace!("Compiler arguments: {:?}", compiler_args);

    // Call the Rust compiler with our custom callback.
    let mut callback = CharonCallbacks::new(options);
    callback.run_compiler(compiler_args)?;
    let CharonCallbacks {
        options,
        transform_ctx,
    } = callback;
    // `transform_ctx` is set by our callbacks when there is no fatal error.
    let ctx = transform_ctx.ok_or(CharonFailure::RustcError)?;
    Ok(Some(DriverOutput { options, ctx }))
}

/// The callbacks for Charon
pub struct CharonCallbacks {
    pub options: CliOpts,
    /// This is to be filled during the extraction; it contains the translated crate.
    transform_ctx: Option<TransformCtx>,
}

impl CharonCallbacks {
    pub fn new(options: options::CliOpts) -> Self {
        Self {
            options,
            transform_ctx: None,
        }
    }

    /// Run rustc with our custom callbacks. `args` is the arguments passed to `rustc`'s
    /// command-line.
    pub fn run_compiler(&mut self, mut args: Vec<String>) -> Result<(), CharonFailure> {
        for extra_flag in self.options.rustc_args.iter().cloned() {
            args.push(extra_flag);
        }

        rustc_driver::catch_fatal_errors(|| {
            rustc_driver::RunCompiler::new(&args, self)
                .run()
                .map_err(|_| CharonFailure::RustcError)
        })
        .map_err(|_| CharonFailure::RustcError)??;
        Ok(())
    }
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

impl Callbacks for CharonCallbacks {
    fn config(&mut self, config: &mut Config) {
        // We use a static to be able to pass data to `override_queries`.
        static SKIP_BORROWCK: AtomicBool = AtomicBool::new(false);
        if self.options.skip_borrowck {
            SKIP_BORROWCK.store(true, Ordering::SeqCst);
        }

        config.override_queries = Some(|_sess, providers| {
            // TODO: catch the MIR in-flight to avoid stealing issues.
            // providers.mir_built = |tcx, def_id| {
            //     let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
            //     let mut mir = mir.steal();
            //     // use the mir
            //     tcx.alloc_steal_mir(mir)
            // };

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
        });

        // Mutate other fields in Config
        disabled_mir_passes(config);
        release_mode(config);
        no_codegen(config);
        polonius(config, self.options.use_polonius);
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
pub struct RunCompilerNormallyCallbacks {
    options: CliOpts,
}
impl Callbacks for RunCompilerNormallyCallbacks {
    fn config(&mut self, config: &mut Config) {
        polonius(config, self.options.use_polonius);
    }
}
impl RunCompilerNormallyCallbacks {
    pub fn new(options: CliOpts) -> Self {
        Self { options }
    }
    /// Run rustc normally. `args` is the arguments passed to `rustc`'s command-line.
    pub fn run_compiler(&mut self, args: Vec<String>) -> Result<(), ()> {
        rustc_driver::RunCompiler::new(&args, self)
            .run()
            .map_err(|_| ())
    }
}
