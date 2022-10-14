#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![feature(is_some_with)]
#![feature(cell_leak)] // For Ref::leak
// For rustdoc: prevents overflows
#![recursion_limit = "256"]

//extern crate env_logger;
extern crate hashlink;
extern crate im;
extern crate linked_hash_set;
extern crate log;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_mir_transform;
extern crate rustc_monomorphize;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate take_mut;

#[macro_use]
mod common;
mod assumed;
mod cli_options;
mod divergent;
mod expressions;
mod expressions_utils;
mod extract_global_assignments;
mod formatter;
mod generics;
mod get_mir;
mod graphs;
mod id_vector;
mod insert_assign_return_unit;
mod llbc_ast;
mod llbc_ast_utils;
mod llbc_export;
mod logger;
mod names;
mod names_utils;
mod reconstruct_asserts;
mod regions_hierarchy;
mod register;
mod regularize_constant_adts;
mod remove_unused_locals;
mod reorder_decls;
mod rust_to_local_ids;
mod simplify_ops;
mod translate_functions_to_im;
mod translate_types;
mod types;
mod types_utils;
mod ullbc_ast;
mod ullbc_ast_utils;
mod ullbc_to_llbc;
mod values;
mod values_utils;

use regex::Regex;
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use serde_json;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::ops::Deref;

/// The callbacks for Charon
struct CharonCallbacks {
    options: cli_options::CliOpts,
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
    /// possible (i.e., after parsing). See [get_mir].
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
/// Rem.: this function comes from Clippy (https://github.com/rust-lang/rust-clippy/blob/42bdfa23d33041642a32950cb39ad92be501a18d/src/driver.rs#L30).
fn arg_value<'a, T: Deref<Target = str>>(
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
fn get_args_source_index<'a, T: Deref<Target = str>>(args: &'a [T]) -> Option<usize> {
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
fn get_args_crate_index<'a, T: Deref<Target = str>>(args: &'a [T]) -> Option<usize> {
    args.iter()
        .enumerate()
        .find(|(_i, s)| Deref::deref(*s) == "--crate-name")
        .map(|(i, _)| {
            assert!(i + 1 < args.len()); // Sanity check
                                         // The argument giving the crate name is the next one
            i + 1
        })
}

fn main() {
    // Initialize the logger
    logger::initialize_logger();

    // Retrieve the executable path - this is not considered an argument,
    // and won't be parsed by CliOpts
    let origin_args: Vec<String> = std::env::args().collect();
    assert!(
        origin_args.len() > 0,
        "Impossible: zero arguments on the command-line!"
    );
    trace!("original arguments (computed by cargo): {:?}", origin_args);

    // The execution path (the path to the current binary) is the first argument
    let exec_path = origin_args[0].clone();

    // Retrieve the Charon options by deserializing them from the environment variable
    // (cargo-charon serialized the arguments and stored them in a specific environment
    // variable before calling cargo with RUSTC_WORKSPACE_WRAPPER=charon-driver).
    let options: cli_options::CliOpts =
        serde_json::from_str(std::env::var(cli_options::CHARON_ARGS).unwrap().as_str()).unwrap();

    // Compute the sysroot (the path to the executable of the compiler):
    // - if it is already in the command line arguments, just retrieve it from there
    // - otherwise retrieve the sysroot from a call to rustc
    let sysroot_arg = arg_value(&origin_args, "--sysroot", |_| true);
    let has_sysroot_arg = sysroot_arg.is_some();
    let sysroot = if has_sysroot_arg {
        sysroot_arg.unwrap().to_string()
    } else {
        let out = std::process::Command::new("rustc")
            .arg("--print=sysroot")
            .current_dir(".")
            .output()
            .unwrap();
        let sysroot = std::str::from_utf8(&out.stdout).unwrap().trim();
        sysroot.to_string()
    };

    // Compute the compiler arguments for Rustc.
    // We first use all the arguments received by charon-driver, except the first
    // one (the first one is the path to the charon-driver executable).
    // Rem.: the second argument is "rustc" (passed by Cargo because RUSTC_WRAPPER
    // is set). It seems not to work when we remove it...
    let mut compiler_args: Vec<String> = origin_args[1..].iter().map(|x| x.clone()).collect();

    // The first argument should be "rustc": replace it with the current executable
    assert!(compiler_args[0] == "rustc");
    compiler_args[0] = exec_path;

    if !has_sysroot_arg {
        compiler_args.extend(vec!["--sysroot".to_string(), sysroot]);
    };
    if options.use_polonius {
        compiler_args.push("-Zpolonius".to_string());
    }

    // In order to have some flexibility in our tests, we give the possibility
    // of specifying the source (the input file which gives the entry to the
    // crate), and of changing the crate name. This allows us to group multiple
    // tests in one crate and call Charon on subsets of this crate (which makes
    // things a lot easier from a maintenance point of view). For instance,
    // we don't extract the whole Charon `tests` (`charon/tests`) crate at once,
    // but rather: `no_nested_borrows`, `hasmap`, `hashmap_main`... Note that
    // this is very specific to the test suite for Charon, so we might remove
    // this in the future. Also, we wouldn't need to do this if we could define
    // several libraries in a single `Cargo.toml` file.
    //
    // If such options are present, we need to update the arguments giving
    // the crate name and the source file.

    // First replace the source name
    let source_index = get_args_source_index(&compiler_args);
    if source_index.is_some() {
        let source_index = source_index.unwrap();
        trace!("source ({}): {}", source_index, compiler_args[source_index]);

        if options.input_file.is_some() {
            compiler_args[source_index] = options
                .input_file
                .as_ref()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string();
        }

        // We replace the crate name only if there is a source name *in the arguments*:
        // we do so because sometimes the driver is called with a crate name but no
        // source. This happens when Cargo needs to retrieve information about
        // the crate.
        if options.crate_name.is_some() {
            let crate_name_index = get_args_crate_index(&compiler_args);
            if crate_name_index.is_some() {
                let crate_name_index = crate_name_index.unwrap();
                trace!(
                    "crate name ({}): {}",
                    crate_name_index,
                    compiler_args[crate_name_index]
                );

                compiler_args[crate_name_index] = options.crate_name.as_ref().unwrap().clone();
            }
            // If there was no crate name given as parameter, introduce one
            else {
                compiler_args.push("--crate-name".to_string());
                compiler_args.push(options.crate_name.as_ref().unwrap().clone());
            }
        }
    }

    trace!("compiler arguments: {:?}", compiler_args);

    // Call the Rust compiler with our custom callback.
    // When we use RUSTC_WRAPPER_WORKSPACE to call charon-driver while piggy-backing
    // on Cargo, the charon-driver is only called on the target (and not its
    // dependencies).
    //
    // Note that the first call to the driver is with "--crate-name ___" and no
    // source file, for Cargo to retrieve some information about the crate.
    // We don't need to check this case in order to use the default Rustc callbacks
    // instead of the Charon callback: because there is nothing to build, Rustc will
    // take care of everything and actually not call us back.
    RunCompiler::new(&compiler_args, &mut CharonCallbacks { options })
        .run()
        .unwrap();
}

/// Translate a crate to LLBC (Low-Level Borrow Calculus).
///
/// This function is a callback function for the Rust compiler.
fn translate(sess: &Session, tcx: TyCtxt, internal: &CharonCallbacks) -> Result<(), ()> {
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
    let registered_decls = register::register_crate(&crate_info, sess, tcx)?;

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

    // # Step 7: simplify the calls to unops and binops
    // Note that we assume that the sequences have been flattened.
    simplify_ops::simplify(&mut llbc_funs, &mut llbc_globals);

    // # Step 8: replace constant (OperandConstantValue) ADTs by regular (Aggregated) ADTs.
    regularize_constant_adts::transform(&mut llbc_funs, &mut llbc_globals);

    // # Step 9: extract statics and constant globals from operands (put them in
    // a let binding). This pass relies on the absence of constant ADTs from
    // the previous step: it does not inspect them (so it would miss globals in
    // constant ADTs).
    extract_global_assignments::transform(&mut llbc_funs, &mut llbc_globals);

    for def in &llbc_funs {
        trace!(
            "# After binop simplification:\n{}\n",
            def.fmt_with_defs(&type_defs, &llbc_funs, &llbc_globals)
        );
    }

    // # Step 10: reconstruct the asserts
    reconstruct_asserts::simplify(&mut llbc_funs, &mut llbc_globals);

    for def in &llbc_funs {
        trace!(
            "# After asserts reconstruction:\n{}\n",
            def.fmt_with_defs(&type_defs, &llbc_funs, &llbc_globals)
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
    insert_assign_return_unit::transform(&mut llbc_funs, &mut llbc_globals);

    // # Step 12: remove the locals which are never used. After doing so, we
    // check that there are no remaining locals with type `Never`.
    remove_unused_locals::transform(&mut llbc_funs, &mut llbc_globals);

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
