#![cfg_attr(feature = "deny-warnings", deny(warnings))]

extern crate rustc_tools_util;

mod cli_options;
mod logger;

use cli_options::{CliOpts, CHARON_ARGS};
use log::trace;
use std::env;
use std::path::PathBuf;
use std::process::Command;
use structopt::StructOpt;

const RUST_VERSION: &'static str = macros::rust_version!();

pub fn main() {
    // We followed the approach used by [rust-clippy](https://github.com/rust-lang/rust-clippy).
    //
    // It works as follows.
    // In order to query the results of the Rustc compiler, we need to implement
    // a driver which calls Rustc while giving it some callbacks.
    // The problem is that finding the proper arguments to call Rustc with can
    // be difficult. For instance, provided the project we want to analyse with
    // Charon has already been built (and in particular its dependencies), it is
    // very difficult to provide the proper `--extern` arguments, indicating
    // where to find the compiled external dependencies. For instance, even if
    // we look in the `target` folder, the compiled depedencies are decorated
    // with a hash, and we don't know where this hash comes from.
    // Computing those arguments is, however, Cargo's responsability. As a
    // consequence, we follow Clippy's approach by piggy-backing on Cargo.  We
    // call Cargo as if we were building the project, but update the environment
    // variable `RUSTC_WORKSPACE_WRAPPER` so that Cargo calls `charon-driver`
    // instead of Rustc upon building the target project. More specifically:
    // Cargo will call Rustc to build the dependencies, *then* will call
    // charon-driver with the arguments it would have given to Rustc to build
    // the target project.
    // Upon being called, charon-driver (see `driver.rs`) will simply call
    // Rustc with the arguments it was provided (and a few minor modifications).
    // Also, in order to transmit options from cargo-charon (this file)
    // to charon-driver (`driver.rs`), we serialize those options and store
    // them in a specific environment variable, so that charon-driver can
    // deserialize them later and use them to guide the extraction in the
    // callbacks.

    // Initialize the logger
    logger::initialize_logger();

    // Parse the command-line
    let options = CliOpts::from_args();
    trace!("Arguments: {:?}", std::env::args());

    // Check that the options are meaningful
    assert!(
        !options.lib || options.bin.is_none(),
        "Can't use --lib and --bin at the same time"
    );

    if let Err(code) = process(&options) {
        std::process::exit(code);
    }
}

fn path() -> PathBuf {
    let mut path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("charon-driver");

    if cfg!(windows) {
        path.set_extension("exe");
    }

    path
}

fn process(options: &CliOpts) -> Result<(), i32> {
    // Compute the arguments of the command to call cargo
    //let cargo_subcommand = "build";
    let cargo_subcommand = "rustc";

    let rust_version = RUST_VERSION;

    let mut cmd = Command::new("cargo");
    cmd.env("RUSTC_WORKSPACE_WRAPPER", path());
    cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());

    if !options.cargo_no_rust_version {
        cmd.arg(rust_version);
    }

    cmd.arg(cargo_subcommand);

    if options.lib {
        cmd.arg("--lib");
    }

    if options.bin.is_some() {
        cmd.arg("--bin");
        cmd.arg(options.bin.as_ref().unwrap().clone());
    }

    if options.release {
        cmd.arg("--release");
    }

    let exit_status = cmd
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo?");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
