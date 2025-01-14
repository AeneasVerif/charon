use crate::translate::translate_crate_to_ullbc;
use charon_lib::export;
use charon_lib::options;
use charon_lib::options::CliOpts;
use charon_lib::transform::{
    Pass, PrintCtxPass, FINAL_CLEANUP_PASSES, INITIAL_CLEANUP_PASSES, LLBC_PASSES, ULLBC_PASSES,
};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use std::fmt;
use std::ops::Deref;
use std::panic::{self, AssertUnwindSafe};
use std::path::PathBuf;

/// The callbacks for Charon
pub struct CharonCallbacks {
    pub options: options::CliOpts,
    /// This is to be filled during the extraction
    pub crate_data: Option<export::CrateData>,
    /// The root of the toolchain.
    pub sysroot: PathBuf,
    pub error_count: usize,
}

pub enum CharonFailure {
    RustcError(usize),
    Panic,
    Serialize,
}

impl fmt::Display for CharonFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CharonFailure::RustcError(error_count) => {
                write!(f, "Compilation encountered {} errors", error_count)?
            }
            CharonFailure::Panic => write!(f, "Compilation panicked")?,
            CharonFailure::Serialize => write!(f, "Could not serialize output file")?,
        }
        Ok(())
    }
}

impl CharonCallbacks {
    pub fn new(options: options::CliOpts, sysroot: PathBuf) -> Self {
        Self {
            options,
            crate_data: None,
            sysroot,
            error_count: 0,
        }
    }

    /// Run rustc with our custom callbacks. `args` is the arguments passed to `rustc`'s
    /// command-line.
    pub fn run_compiler(&mut self, mut args: Vec<String>) -> Result<(), CharonFailure> {
        // Arguments list always start with the executable name. We put a silly value to ensure
        // it's not used for anything.
        args.insert(0, "__CHARON_MYSTERIOUS_FIRST_ARG__".to_string());
        let mut this = AssertUnwindSafe(self);
        panic::catch_unwind(move || {
            let res = rustc_driver::RunCompiler::new(&args, *this).run();
            res.map_err(|_| CharonFailure::RustcError(this.error_count))
        })
        .map_err(|_| CharonFailure::Panic)??;
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
    /// We have to be careful here: we can plug ourselves at several places
    /// (after parsing, after expansion, after analysis). However, the MIR is
    /// modified in place: this means that if we at some point we compute, say,
    /// the promoted MIR, it is possible to query the optimized MIR (because
    /// optimized MIR is further down in the compilation process). However,
    /// it is not possible to query, say, the built MIR (which results from
    /// the conversion to HIR to MIR) because it has been lost.
    /// For this reason, and as we may want to plug ourselves at different
    /// phases of the compilation process, we query the context as early as
    /// possible (i.e., after parsing). See [charon_lib::get_mir].
    fn after_expansion<'tcx>(
        &mut self,
        _c: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // Set up our own `DefId` debug routine.
        rustc_hir::def_id::DEF_ID_DEBUG
            .swap(&(def_id_debug as fn(_, &mut fmt::Formatter<'_>) -> _));

        queries.global_ctxt().unwrap().get_mut().enter(|tcx| {
            let crate_data = translate(tcx, self);
            self.crate_data = Some(crate_data);
        });
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

/// Given a list of arguments, return the index of the source rust file.
/// This works by looking for the first argument matching *.rs, while
/// checking there is at most one such argument.
///
/// Note that the driver is sometimes called without a source, for Cargo to
/// retrieve information about the crate for instance.
pub fn get_args_source_index<T: Deref<Target = str>>(args: &[T]) -> Option<usize> {
    let indices: Vec<usize> = args
        .iter()
        .enumerate()
        .filter_map(|(i, s)| if s.ends_with(".rs") { Some(i) } else { None })
        .collect();
    assert!(indices.len() <= 1);
    if indices.len() == 1 {
        Some(indices[0])
    } else {
        None
    }
}

/// Given a list of arguments, return the index of the crate name
pub fn get_args_crate_index<T: Deref<Target = str>>(args: &[T]) -> Option<usize> {
    args.iter()
        .enumerate()
        .find(|(_i, s)| Deref::deref(*s) == "--crate-name")
        .map(|(i, _)| {
            assert!(i + 1 < args.len()); // Sanity check
                                         // The argument giving the crate name is the next one
            i + 1
        })
}

/// Calculate the list of passes we will run on the crate before outputting it.
pub fn transformation_passes(options: &CliOpts) -> Vec<Pass> {
    let print_original_ullbc = PrintCtxPass::new(
        options.print_original_ullbc,
        format!("# ULLBC after translation from MIR"),
    );
    let print_ullbc = PrintCtxPass::new(options.print_ullbc, {
        let next_phase = if options.ullbc {
            "serialization"
        } else {
            "control-flow reconstruction"
        };
        format!("# Final ULLBC before {next_phase}")
    });
    let print_llbc = PrintCtxPass::new(
        options.print_llbc,
        format!("# Final LLBC before serialization"),
    );

    let mut passes: Vec<Pass> = vec![];
    passes.push(Pass::NonBody(print_original_ullbc));
    passes.extend(INITIAL_CLEANUP_PASSES);
    passes.extend(ULLBC_PASSES);
    passes.push(Pass::NonBody(print_ullbc));

    // # There are two options:
    // - either the user wants the unstructured LLBC, in which case we stop there
    // - or they want the structured LLBC, in which case we reconstruct the control-flow and apply
    // more micro-passes
    if !options.ullbc {
        passes.extend(LLBC_PASSES);
        passes.push(Pass::NonBody(print_llbc));
    }

    passes.extend(FINAL_CLEANUP_PASSES);
    passes
}

/// Translate a crate to LLBC (Low-Level Borrow Calculus).
///
/// This function is a callback function for the Rust compiler. The `tcx` parameter allows us to
/// interact with compiler internals to explore the crates and translate relevant items.
pub fn translate(tcx: TyCtxt, internal: &mut CharonCallbacks) -> export::CrateData {
    trace!();
    let options = &internal.options;

    // Translate the contents of the crate.
    let mut transform_ctx =
        translate_crate_to_ullbc::translate(options, tcx, internal.sysroot.clone());

    // The bulk of the translation is done, we no longer need to interact with rustc internals. We
    // run several passes that simplify the items and cleanup the bodies.
    for pass in transformation_passes(options) {
        trace!("# Starting pass {}", pass.name());
        pass.run(&mut transform_ctx)
    }

    // Update the error count
    internal.error_count = transform_ctx.errors.borrow().error_count;

    export::CrateData::new(&transform_ctx)
}
