//! The Charon driver, which calls Rustc with callbacks to compile some Rust
//! crate to LLBC.

#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![feature(is_some_and)]
#![feature(cell_leak)] // For Ref::leak
// For rustdoc: prevents overflows
#![recursion_limit = "256"]

extern crate hashlink;
extern crate im;
extern crate linked_hash_set;
extern crate log;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_error_messages;
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
mod driver;
mod export;
mod expressions;
mod expressions_utils;
mod extract_global_assignments;
mod formatter;
mod gast;
mod gast_utils;
mod generics;
mod get_mir;
mod graphs;
mod id_vector;
mod insert_assign_return_unit;
mod llbc_ast;
mod llbc_ast_utils;
mod logger;
mod meta;
mod meta_utils;
mod names;
mod names_utils;
mod reconstruct_asserts;
mod regions_hierarchy;
mod register;
mod regularize_constant_adts;
mod remove_drop_never;
mod remove_read_discriminant;
mod remove_unused_locals;
mod reorder_decls;
mod rust_to_local_ids;
mod translate_functions_to_ullbc;
mod translate_types;
mod types;
mod types_utils;
mod ullbc_ast;
mod ullbc_ast_utils;
mod ullbc_to_llbc;
mod values;
mod values_utils;

use crate::driver::{arg_value, get_args_crate_index, get_args_source_index, CharonCallbacks};
use rustc_driver::RunCompiler;

fn main() {
    // Initialize the logger
    logger::initialize_logger();

    // Retrieve the executable path - this is not considered an argument,
    // and won't be parsed by CliOpts
    let origin_args: Vec<String> = std::env::args().collect();
    assert!(
        !origin_args.is_empty(),
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
    let mut compiler_args: Vec<String> = origin_args[1..].to_vec();

    // The first argument should be "rustc": replace it with the current executable
    assert!(compiler_args[0] == "rustc");
    compiler_args[0] = exec_path;

    if !has_sysroot_arg {
        compiler_args.extend(vec!["--sysroot".to_string(), sysroot]);
    }
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
    if let Some(source_index) = source_index {
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
            if let Some(crate_name_index) = crate_name_index {
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

    trace!("Compiler arguments: {:?}", compiler_args);

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
