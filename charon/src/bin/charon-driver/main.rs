//! The Charon driver, which calls Rustc with callbacks to compile some Rust
//! crate to LLBC.
#![feature(rustc_private)]
#![expect(incomplete_features)]
#![feature(box_patterns)]
#![feature(deref_patterns)]
#![feature(if_let_guard)]
#![feature(iter_array_chunks)]
#![feature(iterator_try_collect)]
#![feature(let_chains)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_attr;
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

use crate::driver::{arg_values, CharonCallbacks, CharonFailure, RunCompilerNormallyCallbacks};
use charon_lib::{logger, options};
use std::{env, panic};

fn main() {
    // Initialize the logger
    logger::initialize_logger();

    // Retrieve the executable path - this is not considered an argument,
    // and won't be parsed by CliOpts
    let origin_args: Vec<String> = env::args().collect();
    assert!(
        !origin_args.is_empty(),
        "Impossible: zero arguments on the command-line!"
    );
    trace!("original arguments (computed by cargo): {:?}", origin_args);

    // Compute the compiler arguments for Rustc.
    // We first use all the arguments received by charon-driver, except the first two.
    // Rem.: the first argument is the path to the charon-driver executable.
    // Rem.: the second argument is "rustc" (passed by Cargo because RUSTC_WRAPPER is set).
    assert_eq!(
        std::path::Path::new(&origin_args[1]).file_stem(),
        Some("rustc".as_ref()),
        "The second argument for charon-driver must be a path to rustc."
    );
    let mut compiler_args: Vec<String> = origin_args[2..].to_vec();

    // Retrieve the Charon options by deserializing them from the environment variable
    // (cargo-charon serialized the arguments and stored them in a specific environment
    // variable before calling cargo with RUSTC_WORKSPACE_WRAPPER=charon-driver).
    let options: options::CliOpts = match env::var(options::CHARON_ARGS) {
        Ok(opts) => serde_json::from_str(opts.as_str()).unwrap(),
        Err(_) => Default::default(),
    };

    if options.use_polonius {
        compiler_args.push("-Zpolonius".to_string());
    }

    // Cargo calls the driver twice. The first call to the driver is with "--crate-name ___" and no
    // source file, for Cargo to retrieve some information about the crate.
    let is_dry_run = arg_values(&origin_args, "--crate-name")
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
    let is_target = arg_values(&origin_args, "--target").next().is_some();

    if is_dry_run || is_workspace_dependency || !is_target {
        trace!("Skipping charon; running compiler normally instead.");
        // In this case we run the compiler normally.
        RunCompilerNormallyCallbacks
            .run_compiler(compiler_args)
            .unwrap();
        return;
    }

    // Always compile in release mode: in effect, we want to analyze the released
    // code. Also, rustc inserts a lot of dynamic checks in debug mode, that we
    // have to clean. Full list of `--release` flags:
    // https://doc.rust-lang.org/cargo/reference/profiles.html#release
    compiler_args.push("-Copt-level=3".to_string());
    compiler_args.push("-Coverflow-checks=false".to_string());
    compiler_args.push("-Cdebug-assertions=false".to_string());

    for extra_flag in options.rustc_args.iter().cloned() {
        compiler_args.push(extra_flag);
    }

    trace!("Compiler arguments: {:?}", compiler_args);

    // Call the Rust compiler with our custom callback.
    let mut callback = CharonCallbacks::new(options);
    let mut callback_ = panic::AssertUnwindSafe(&mut callback);
    let res = panic::catch_unwind(move || callback_.run_compiler(compiler_args))
        .map_err(|_| CharonFailure::Panic)
        .and_then(|x| x);
    let CharonCallbacks {
        options,
        error_count,
        ..
    } = callback;

    // # Final step: generate the files.
    let mut res = match res {
        Ok(_) if options.no_serialize => Ok(()),
        Ok(crate_data) => {
            let dest_file = match options.dest_file.clone() {
                Some(f) => f,
                None => {
                    let mut target_filename = options.dest_dir.clone().unwrap_or_default();
                    let crate_name = &crate_data.translated.crate_name;
                    let extension = if options.ullbc { "ullbc" } else { "llbc" };
                    target_filename.push(format!("{crate_name}.{extension}"));
                    target_filename
                }
            };
            trace!("Target file: {:?}", dest_file);
            crate_data
                .serialize_to_file(&dest_file)
                .map_err(|()| CharonFailure::Serialize)
        }
        Err(e) => Err(e),
    };

    if res.is_ok() && options.error_on_warnings && error_count != 0 {
        res = Err(CharonFailure::CharonError(error_count));
    }

    match res {
        Ok(()) => {
            if error_count != 0 {
                let msg = format!("The extraction generated {} warnings", error_count);
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
