#![cfg_attr(feature = "deny-warnings", deny(warnings))]
// warn on lints, that are included in `rust-lang/rust`s bootstrap
//#![warn(rust_2018_idioms, unused_lifetimes)]
//#![feature(proc_macro_span)]

extern crate rustc_tools_util;

mod cli_options;
mod logger;

use cli_options::{CliOpts, CHARON_ARGS};
use log::info;
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
    let cargo_subcommand = "build";

    let rust_version = RUST_VERSION;

    let mut cmd = Command::new("cargo");
    cmd.env("RUSTC_WORKSPACE_WRAPPER", path());
    cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());
    cmd.arg(rust_version);
    cmd.arg(cargo_subcommand);

    //    cmd.arg(options.input_file.to_str().unwrap());

    /*    info!("RUSTC: {:?}", path());
    info!(
        "CHARON_ARGS: {:?}",
        serde_json::to_string(&options).unwrap()
    );
    info!("cmd: {:?}", cmd);*/

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
