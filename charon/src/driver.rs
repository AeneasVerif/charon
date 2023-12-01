use crate::cli_options;
use crate::export;
use crate::get_mir::MirLevel;
use crate::index_to_function_calls;
use crate::insert_assign_return_unit;
use crate::ops_to_function_calls;
use crate::reconstruct_asserts;
use crate::remove_drop_never;
use crate::remove_dynamic_checks;
use crate::remove_nops;
use crate::remove_read_discriminant;
use crate::remove_unused_locals;
use crate::reorder_decls;
use crate::simplify_constants;
use crate::translate_crate_to_ullbc;
use crate::translate_ctx;
use crate::ullbc_to_llbc;
use regex::Regex;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::ops::Deref;

/// The callbacks for Charon
pub struct CharonCallbacks {
    pub options: cli_options::CliOpts,
    /// This is to be filled during the extraction
    pub error_count: usize,
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
    /// possible (i.e., after parsing). See [crate::get_mir].
    fn after_parsing<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries
            .global_ctxt()
            .unwrap()
            .get_mut()
            .enter(|tcx| {
                let session = c.session();
                translate(session, tcx, self)
            })
            .unwrap();
        Compilation::Stop
    }
}

/// If a command-line option matches `find_arg`, then apply the predicate `pred` on its value. If
/// true, then return it. The parameter is assumed to be either `--arg=value` or `--arg value`.
/// Rem.: this function comes from Clippy <https://github.com/rust-lang/rust-clippy/blob/42bdfa23d33041642a32950cb39ad92be501a18d/src/driver.rs#L30>.
pub fn arg_value<'a, T: Deref<Target = str>>(
    args: &'a [T],
    find_arg: &str,
    pred: impl Fn(&str) -> bool,
) -> Option<&'a str> {
    let mut args = args.iter().map(Deref::deref);
    while let Some(arg) = args.next() {
        let mut arg = arg.splitn(2, '=');
        if arg.next() != Some(find_arg) {
            continue;
        }

        match arg.next().or_else(|| args.next()) {
            Some(v) if pred(v) => return Some(v),
            _ => {}
        }
    }
    None
}

/// Given a list of arguments, return the index of the source rust file.
/// This works by looking for the first argument matching *.rs, while
/// checking there is at most one such argument.
///
/// Note that the driver is sometimes called without a source, for Cargo to
/// retrieve information about the crate for instance.
pub fn get_args_source_index<T: Deref<Target = str>>(args: &[T]) -> Option<usize> {
    let re = Regex::new(r".*\.rs").unwrap();
    let indices: Vec<usize> = args
        .iter()
        .enumerate()
        .filter_map(|(i, s)| if re.is_match(s) { Some(i) } else { None })
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

/// Translate a crate to LLBC (Low-Level Borrow Calculus).
///
/// This function is a callback function for the Rust compiler.
#[allow(clippy::result_unit_err)]
pub fn translate(sess: &Session, tcx: TyCtxt, internal: &mut CharonCallbacks) -> Result<(), ()> {
    trace!();
    let options = &internal.options;

    // Retrieve the crate name: if the user specified a custom name, use
    // it, otherwise retrieve it from Rustc.
    let crate_name: String = options.crate_name.as_deref().map_or_else(
        || {
            tcx.crate_name(rustc_span::def_id::LOCAL_CRATE)
                .to_ident_string()
        },
        |x: &str| x.to_string(),
    );
    trace!("# Crate: {}", crate_name);

    // Adjust the level of MIR we extract, depending on the options
    let mir_level = if options.mir_optimized {
        MirLevel::Optimized
    } else if options.mir_promoted {
        MirLevel::Promoted
    } else {
        MirLevel::Built
    };

    // Some important notes about crates and how to interact with rustc:
    // - when calling rustc, we should give it the root of the crate, for
    //   instance the "main.rs" file. From there, rustc will load all the
    //   *modules* (i.e., files) in the crate
    // - whenever there is a `mod MODULE` in a file (for instance, in the
    //   "main.rs" file), it becomes a Module HIR item

    let crate_info = translate_ctx::CrateInfo {
        crate_name: crate_name.clone(),
        opaque_mods: HashSet::from_iter(options.opaque_modules.clone().into_iter()),
    };

    // # Translate the declarations in the crate.
    // We translate the declarations in an ad-hoc order, and do not group
    // the mutually recursive groups - we do this in the next step.
    let mut ctx = translate_crate_to_ullbc::translate(crate_info, options, sess, tcx, mir_level);

    trace!("# After translation from MIR:\n\n{}\n", ctx);

    if options.print_ullbc {
        info!("# ULLBC after translation from MIR:\n\n{}\n", ctx);
    }

    // # Reorder the graph of dependencies and compute the strictly
    // connex components to:
    // - compute the order in which to extract the definitions
    // - find the recursive definitions
    // - group the mutually recursive definitions
    let ordered_decls = reorder_decls::reorder_declarations(&ctx);

    //
    // =================
    // **Micro-passes**:
    // =================
    // At this point, the bulk of the translation is done. From now onwards,
    // we simply apply some micro-passes to make the code cleaner, before
    // serializing the result.

    // # Micro-pass: desugar the constants to other values/operands as much
    // as possible.
    simplify_constants::transform(&mut ctx);

    // # There are two options:
    // - either the user wants the unstructured LLBC, in which case we stop there
    // - or they want the structured LLBC, in which case we reconstruct the
    //   control-flow and apply micro-passes

    if options.ullbc {
        // # Extract the files
        export::export_ullbc(
            &ctx,
            crate_name,
            &ordered_decls,
            &ctx.fun_decls,
            &ctx.global_decls,
            &options.dest_dir,
        )?;
    } else {
        // # Go from ULLBC to LLBC (Low-Level Borrow Calculus) by reconstructing
        // the control flow.
        let (mut llbc_funs, mut llbc_globals) = ullbc_to_llbc::translate_functions(&ctx);

        if options.print_built_llbc {
            let llbc_ctx = crate::translate_ctx::LlbcTransCtx {
                ctx: &ctx,
                llbc_globals: &llbc_globals,
                llbc_funs: &llbc_funs,
            };
            info!(
                "# LLBC resulting from control-flow reconstruction:\n\n{}\n",
                llbc_ctx
            );
        }

        // # Micro-pass: the first local variable of closures is the
        // closure itself (it seems). This is not consistent with the fact
        //

        // # Micro-pass: remove the dynamic checks for array/slice bounds
        // and division by zero.
        // **WARNING**: this pass uses the fact that the dynamic checks
        // introduced by Rustc use a special "assert" construct. Because of
        // this, it must happen *before* the [reconstruct_asserts] pass.
        // See the comments in [crate::remove_dynamic_checks].
        remove_dynamic_checks::transform(&mut ctx, &mut llbc_funs, &mut llbc_globals);

        // # Micro-pass: reconstruct the asserts
        reconstruct_asserts::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        // TODO: we should mostly use the TransCtx to format declarations
        use crate::formatter::{Formatter, IntoFormatter};
        for (_, def) in &llbc_funs {
            trace!(
                "# After asserts reconstruction:\n{}\n",
                ctx.into_fmt().format_object(def)
            );
        }

        // # Micro-pass: replace some unops/binops and the array aggregates with
        // function calls (introduces: ArrayToSlice, etc.)
        ops_to_function_calls::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        // # Micro-pass: replace the arrays/slices index operations with function
        // calls.
        // (introduces: ArrayIndexShared, ArrayIndexMut, etc.)
        index_to_function_calls::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        // # Micro-pass: Remove the discriminant reads (merge them with the switches)
        remove_read_discriminant::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        // # Micro-pass: add the missing assignments to the return value.
        // When the function return type is unit, the generated MIR doesn't
        // set the return value to `()`. This can be a concern: in the case
        // of Aeneas, it means the return variable contains ⊥ upon returning.
        // For this reason, when the function has return type unit, we insert
        // an extra assignment just before returning.
        // This also applies to globals (for checking or executing code before
        // the main or at compile-time).
        insert_assign_return_unit::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        // # Micro-pass: remove the drops of locals whose type is `Never` (`!`). This
        // is in preparation of the next transformation.
        remove_drop_never::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        // # Micro-pass: remove the locals which are never used. After doing so, we
        // check that there are no remaining locals with type `Never`.
        remove_unused_locals::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        // # Micro-pass (not necessary, but good for cleaning): remove the
        // useless no-ops.
        remove_nops::transform(&ctx, &mut llbc_funs, &mut llbc_globals);

        trace!("# Final LLBC:\n");
        for (_, def) in &llbc_funs {
            trace!("#{}\n", ctx.into_fmt().format_object(def));
        }

        let llbc_ctx = crate::translate_ctx::LlbcTransCtx {
            ctx: &ctx,
            llbc_globals: &llbc_globals,
            llbc_funs: &llbc_funs,
        };
        trace!("# About to export:\n\n{}\n", llbc_ctx);
        if options.print_llbc {
            info!("# Final LLBC before serialization:\n\n{}\n", llbc_ctx);
        }

        // # Final step: generate the files.
        export::export_llbc(
            &ctx,
            crate_name,
            &ordered_decls,
            &llbc_funs,
            &llbc_globals,
            &options.dest_dir,
        )?;
    }
    trace!("Done");

    // Update the error count
    internal.error_count = ctx.error_count;

    Ok(())
}
