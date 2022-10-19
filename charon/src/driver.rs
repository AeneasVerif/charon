#![allow(dead_code)]

use crate::cli_options;
use crate::divergent;
use crate::extract_global_assignments;
use crate::get_mir::MirLevel;
use crate::insert_assign_return_unit;
use crate::llbc_ast::{CtxNames, FunDeclId, GlobalDeclId};
use crate::llbc_export;
use crate::reconstruct_asserts;
use crate::register;
use crate::regularize_constant_adts;
use crate::remove_unused_locals;
use crate::reorder_decls;
use crate::rust_to_local_ids;
use crate::simplify_ops;
use crate::translate_functions_to_im;
use crate::translate_types;
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
            .peek_mut()
            .enter(|tcx| {
                let session = c.session();
                translate(session, tcx, &self)
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
pub fn get_args_source_index<'a, T: Deref<Target = str>>(args: &'a [T]) -> Option<usize> {
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
pub fn get_args_crate_index<'a, T: Deref<Target = str>>(args: &'a [T]) -> Option<usize> {
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
pub fn translate(sess: &Session, tcx: TyCtxt, internal: &CharonCallbacks) -> Result<(), ()> {
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
    } else {
        MirLevel::Built
    };

    // Some important notes about crates and how to interact with rustc:
    // - when calling rustc, we should give it the root of the crate, for
    //   instance the "main.rs" file. From there, rustc will load all the
    //   *modules* (i.e., files) in the crate
    // - whenever there is a `mod MODULE` in a file (for instance, in the
    //   "main.rs" file), it becomes a Module HIR item

    // # Step 1: check and register all the definitions, to build the graph
    // of dependencies between them (we need to know in which
    // order to extract the definitions, and which ones are mutually
    // recursive). While building this graph, we perform as many checks as
    // we can to make sure the code is in the proper rust subset. Those very
    // early steps mostly involve checking whether some features are used or
    // not (ex.: raw pointers, inline ASM, etc.). More complex checks are
    // performed later. In general, whenever there is ambiguity on the potential
    // step in which a step could be performed, we perform it as soon as possible.
    // Building the graph of dependencies allows us to translate the definitions
    // in the proper order, and to figure out which definitions are mutually
    // recursive.
    // We iterate over the HIR items, and explore their MIR bodies/ADTs/etc.
    // (when those exist - for instance, type aliases don't have MIR translations
    // so we just ignore them).
    let crate_info = register::CrateInfo {
        crate_name: crate_name.clone(),
        opaque_mods: HashSet::from_iter(options.opaque_modules.clone().into_iter()),
    };
    let registered_decls = register::register_crate(&crate_info, sess, tcx, mir_level)?;

    // # Step 2: reorder the graph of dependencies and compute the strictly
    // connex components to:
    // - compute the order in which to extract the definitions
    // - find the recursive definitions
    // - group the mutually recursive definitions
    let ordered_decls = reorder_decls::reorder_declarations(&registered_decls)?;

    // # Step 3: generate identifiers for the types and functions, and compute
    // the mappings from rustc identifiers to our own identifiers
    let ordered_decls = rust_to_local_ids::rust_to_local_ids(&ordered_decls);

    // # Step 4: translate the types
    let (types_constraints, type_defs) = translate_types::translate_types(tcx, &ordered_decls)?;

    // # Step 5: translate the functions to IM (our Internal representation of MIR).
    // Note that from now onwards, both type and function definitions have been
    // translated to our internal ASTs: we don't interact with rustc anymore.
    let (im_fun_defs, im_global_defs) = translate_functions_to_im::translate_functions(
        tcx,
        &ordered_decls,
        &types_constraints,
        &type_defs,
        mir_level,
    )?;

    // # Step 6: go from IM to LLBC (Low-Level Borrow Calculus) by reconstructing
    // the control flow.
    let (mut llbc_funs, mut llbc_globals) = ullbc_to_llbc::translate_functions(
        options.no_code_duplication,
        &type_defs,
        &im_fun_defs,
        &im_global_defs,
    );

    //
    // =================
    // **Micro-passes**:
    // =================
    // At this point, the bulk of the translation is done. From now onwards,
    // we simply apply some micro-passes to make the code cleaner, before
    // serializing the result.
    //

    // Compute the list of function and global names in the context.
    // We need this for pretty-printing (i.e., debugging) purposes.
    // We could use the [FunDecls] and [GlobalDecls] contexts, but we often
    // mutably borrow them to modify them in place, which prevents us from
    // using them for pretty-printing purposes (we would need to create shared
    // borrows over already mutably borrowed values).
    let fun_names: FunDeclId::Vector<String> =
        FunDeclId::Vector::from_iter(llbc_funs.iter().map(|d| d.name.to_string()));
    let global_names: GlobalDeclId::Vector<String> =
        GlobalDeclId::Vector::from_iter(llbc_globals.iter().map(|d| d.name.to_string()));
    let fmt_ctx = CtxNames::new(&type_defs, &fun_names, &global_names);

    // # Step 7: simplify the calls to unops and binops
    // Note that we assume that the sequences have been flattened.
    simplify_ops::simplify(&fmt_ctx, &mut llbc_funs, &mut llbc_globals);

    // # Step 8: replace constant ([OperandConstantValue]) ADTs by regular
    // (Aggregated) ADTs.
    regularize_constant_adts::transform(&fmt_ctx, &mut llbc_funs, &mut llbc_globals);

    // # Step 9: extract statics and constant globals from operands (put them in
    // a let binding). This pass relies on the absence of constant ADTs from
    // the previous step: it does not inspect them (and would thus miss globals
    // in constant ADTs).
    extract_global_assignments::transform(&fmt_ctx, &mut llbc_funs, &mut llbc_globals);

    for def in &llbc_funs {
        trace!(
            "# After binop simplification:\n{}\n",
            def.fmt_with_decls(&type_defs, &llbc_funs, &llbc_globals)
        );
    }

    // # Step 10: reconstruct the asserts
    reconstruct_asserts::transform(&fmt_ctx, &mut llbc_funs, &mut llbc_globals);

    for def in &llbc_funs {
        trace!(
            "# After asserts reconstruction:\n{}\n",
            def.fmt_with_decls(&type_defs, &llbc_funs, &llbc_globals)
        );
    }

    // # Step 11: add the missing assignments to the return value.
    // When the function return type is unit, the generated MIR doesn't
    // set the return value to `()`. This can be a concern: in the case
    // of Aeneas, it means the return variable contains ⊥ upon returning.
    // For this reason, when the function has return type unit, we insert
    // an extra assignment just before returning.
    // This also applies to globals (for checking or executing code before
    // the main or at compile-time).
    insert_assign_return_unit::transform(&fmt_ctx, &mut llbc_funs, &mut llbc_globals);

    // # Step 12: remove the locals which are never used. After doing so, we
    // check that there are no remaining locals with type `Never`.
    remove_unused_locals::transform(&fmt_ctx, &mut llbc_funs, &mut llbc_globals);

    // # Step 13: compute which functions are potentially divergent. A function
    // is potentially divergent if it is recursive, contains a loop or transitively
    // calls a potentially divergent function.
    // Note that in the future, we may complement this basic analysis with a
    // finer analysis to detect recursive functions which are actually total
    // by construction.
    // Because we don't have loops, constants are not yet touched.
    let _divergent = divergent::compute_divergent_functions(&ordered_decls, &llbc_funs);

    // # Step 14: generate the files.
    llbc_export::export(
        crate_name.clone(),
        &ordered_decls,
        &type_defs,
        &llbc_funs,
        &llbc_globals,
        &options.dest_dir,
    )?;

    trace!("Done");

    Ok(())
}
