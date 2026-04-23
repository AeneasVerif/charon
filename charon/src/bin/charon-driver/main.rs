//! The Charon driver, which calls Rustc with callbacks to compile some Rust
//! crate to LLBC.
#![feature(rustc_private)]
#![allow(clippy::useless_format)]
#![allow(clippy::manual_map)]
#![allow(clippy::mem_replace_with_default)]
#![allow(clippy::derivable_impls)]
#![allow(clippy::borrowed_box)]
#![allow(clippy::field_reassign_with_default)]
#![expect(incomplete_features)]
#![feature(box_patterns)]
#![feature(deref_patterns)]
#![feature(if_let_guard)]
#![feature(iter_array_chunks)]
#![feature(iterator_try_collect)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_error_messages;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
extern crate charon_lib;

mod driver;
mod translate;

use charon_lib::{
    export, logger,
    options::CliOpts,
    transform::{
        FINAL_CLEANUP_PASSES, INITIAL_CLEANUP_PASSES, LLBC_PASSES, Pass, PrintCtxPass,
        SHARED_FINALIZING_PASSES, ULLBC_PASSES,
    },
};
use std::{fmt, panic};

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

/// Calculate the list of passes we will run on the crate before outputting it.
pub fn transformation_passes(options: &CliOpts) -> Vec<Pass> {
    let mut passes: Vec<Pass> = vec![];

    passes.push(Pass::NonBody(PrintCtxPass::new(
        options.print_original_ullbc,
        "# ULLBC after translation from MIR".to_string(),
    )));

    passes.extend(INITIAL_CLEANUP_PASSES);
    passes.extend(ULLBC_PASSES);

    if !options.ullbc {
        // If we're reconstructing control-flow, print the ullbc here.
        passes.push(Pass::NonBody(PrintCtxPass::new(
            options.print_ullbc,
            "# Final ULLBC before control-flow reconstruction".to_string(),
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
            "# Final ULLBC before serialization".to_string(),
        )));
    } else {
        passes.push(Pass::NonBody(PrintCtxPass::new(
            options.print_llbc,
            "# Final LLBC before serialization".to_string(),
        )));
    }

    // Run the final passes after pretty-printing so that we get some output even if check_generics
    // fails.
    passes.extend(FINAL_CLEANUP_PASSES);
    passes
}

/// Run charon. Returns the number of warnings generated.
fn run_charon() -> Result<usize, CharonFailure> {
    // Run the driver machinery.
    let Some((mut ctx, options)) = driver::run_rustc_driver()? else {
        // We didn't run charon.
        return Ok(0);
    };

    // The bulk of the translation is done, we no longer need to interact with rustc internals. We
    // run several passes that simplify the items and cleanup the bodies.
    for pass in transformation_passes(&options) {
        trace!("# Starting pass {}", pass.name());
        pass.run(&mut ctx);
    }

    let error_count = ctx.errors.borrow().error_count;

    // # Final step: generate the files.
    if !options.no_serialize {
        let dest_file = options.target_filename(&ctx.translated.crate_name);
        trace!("Target file: {:?}", dest_file);
        export::CrateData::new(ctx)
            .serialize_to_file(&dest_file)
            .map_err(|()| CharonFailure::Serialize)?;
    }

    if options.error_on_warnings && error_count != 0 {
        return Err(CharonFailure::CharonError(error_count));
    }

    Ok(error_count)
}

fn main() {
    // Initialize the logger
    logger::initialize_logger();

    // Catch any and all panics coming from charon to display a clear error.
    let res = panic::catch_unwind(run_charon)
        .map_err(|_| CharonFailure::Panic)
        .and_then(|x| x);

    match res {
        Ok(warn_count) => {
            if warn_count != 0 {
                let msg = format!("The extraction generated {} warnings", warn_count);
                eprintln!("warning: {}", msg);
            }
        }
        Err(err) => {
            log::error!("{err}");
            let exit_code = match err {
                CharonFailure::CharonError(_) | CharonFailure::Serialize => 1,
                CharonFailure::RustcError => 2,
                // This is a real panic, exit with the standard rust panic error code.
                CharonFailure::Panic => 101,
            };
            std::process::exit(exit_code);
        }
    }
}
