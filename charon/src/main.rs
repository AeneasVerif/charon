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
