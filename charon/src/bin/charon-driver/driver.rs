use crate::translate::translate_crate_to_ullbc;
use charon_lib::options::CliOpts;
use charon_lib::transform::{
    Pass, PrintCtxPass, FINAL_CLEANUP_PASSES, INITIAL_CLEANUP_PASSES, LLBC_PASSES, ULLBC_PASSES,
};
use charon_lib::transform::{TransformCtx, SHARED_FINALIZING_PASSES};
use charon_lib::{export, options};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};
use std::fmt;
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, Ordering};

mod config;

/// The callbacks for Charon
pub struct CharonCallbacks {
    pub options: options::CliOpts,
    /// This is to be filled during the extraction; it contains the translated crate.
    transform_ctx: Option<TransformCtx>,
    pub error_count: usize,
}

pub enum CharonFailure {
    /// The usize is the number of errors.
    CharonError(usize),
    RustcError,
    Panic,
    Serialize,
}

impl fmt::Display for CharonFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CharonFailure::RustcError => write!(f, "Code failed to compile")?,
            CharonFailure::CharonError(err_count) => write!(
                f,
                "Charon failed to translate this code ({err_count} errors)"
            )?,
            CharonFailure::Panic => write!(f, "Compilation panicked")?,
            CharonFailure::Serialize => write!(f, "Could not serialize output file")?,
        }
        Ok(())
    }
}

impl CharonCallbacks {
    pub fn new(options: options::CliOpts) -> Self {
        Self {
            options,
            transform_ctx: None,
            error_count: 0,
        }
    }

    /// Run rustc with our custom callbacks. `args` is the arguments passed to `rustc`'s
    /// command-line.
    pub fn run_compiler(
        &mut self,
        mut args: Vec<String>,
    ) -> Result<export::CrateData, CharonFailure> {
        // Arguments list always start with the executable name. We put a silly value to ensure
        // it's not used for anything.
        args.insert(0, "__CHARON_MYSTERIOUS_FIRST_ARG__".to_string());
        rustc_driver::catch_fatal_errors(|| {
            let res = rustc_driver::RunCompiler::new(&args, self).run();
            res.map_err(|_| CharonFailure::RustcError)
        })
        .map_err(|_| CharonFailure::RustcError)??;
        // `ctx` is set by our callbacks when there is no fatal error.
        let ctx = self
            .transform_ctx
            .as_mut()
            .ok_or(CharonFailure::RustcError)?;

        let crate_data = transform(ctx, &self.options);
        self.error_count = ctx.errors.borrow().error_count;
        Ok(crate_data)
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
    fn config(&mut self, config: &mut rustc_interface::Config) {
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
        config::disabled_mir_passes(config);
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
pub struct RunCompilerNormallyCallbacks;
impl Callbacks for RunCompilerNormallyCallbacks {}
impl RunCompilerNormallyCallbacks {
    /// Run rustc normally. `args` is the arguments passed to `rustc`'s command-line.
    pub fn run_compiler(&mut self, mut args: Vec<String>) -> Result<(), ()> {
        // Arguments list always start with the executable name. We put a silly value to ensure
        // it's not used for anything.
        args.insert(0, "__CHARON_MYSTERIOUS_FIRST_ARG__".to_string());
        rustc_driver::RunCompiler::new(&args, self)
            .run()
            .map_err(|_| ())
    }
}

/// Returns the values of the command-line options that match `find_arg`. The options are built-in
/// to be of the form `--arg=value` or `--arg value`.
pub fn arg_values<'a, T: Deref<Target = str>>(
    args: &'a [T],
    needle: &'a str,
) -> impl Iterator<Item = &'a str> {
    struct ArgFilter<'a, T> {
        args: std::slice::Iter<'a, T>,
        needle: &'a str,
    }
    impl<'a, T: Deref<Target = str>> Iterator for ArgFilter<'a, T> {
        type Item = &'a str;
        fn next(&mut self) -> Option<Self::Item> {
            while let Some(arg) = self.args.next() {
                let mut split_arg = arg.splitn(2, '=');
                if split_arg.next() == Some(self.needle) {
                    return match split_arg.next() {
                        // `--arg=value` form
                        arg @ Some(_) => arg,
                        // `--arg value` form
                        None => self.args.next().map(|x| x.deref()),
                    };
                }
            }
            None
        }
    }
    ArgFilter {
        args: args.iter(),
        needle,
    }
}

/// Calculate the list of passes we will run on the crate before outputting it.
pub fn transformation_passes(options: &CliOpts) -> Vec<Pass> {
    let mut passes: Vec<Pass> = vec![];

    passes.push(Pass::NonBody(PrintCtxPass::new(
        options.print_original_ullbc,
        format!("# ULLBC after translation from MIR"),
    )));

    passes.extend(INITIAL_CLEANUP_PASSES);
    passes.extend(ULLBC_PASSES);

    if !options.ullbc {
        // If we're reconstructing control-flow, print the ullbc here.
        passes.push(Pass::NonBody(PrintCtxPass::new(
            options.print_ullbc,
            format!("# Final ULLBC before control-flow reconstruction"),
        )));
    }

    if !options.ullbc {
        passes.extend(LLBC_PASSES);
    }
    passes.extend(SHARED_FINALIZING_PASSES);

    if options.ullbc {
        // If we're not reconstructing control-flow, print the ullbc after finalizing passes.
        passes.push(Pass::NonBody(PrintCtxPass::new(
            options.print_ullbc,
            format!("# Final ULLBC before serialization"),
        )));
    } else {
        passes.push(Pass::NonBody(PrintCtxPass::new(
            options.print_llbc,
            format!("# Final LLBC before serialization"),
        )));
    }

    // Run the final passes after pretty-printing so that we get some output even if check_generics
    // fails.
    passes.extend(FINAL_CLEANUP_PASSES);
    passes
}

/// Apply the transformation passes to a translated crate.
pub fn transform(ctx: &mut TransformCtx, options: &CliOpts) -> export::CrateData {
    // The bulk of the translation is done, we no longer need to interact with rustc internals. We
    // run several passes that simplify the items and cleanup the bodies.
    for pass in transformation_passes(options) {
        trace!("# Starting pass {}", pass.name());
        pass.run(ctx);
    }

    export::CrateData::new(&ctx)
}
