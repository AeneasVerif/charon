//! Charon is a tool which compiles Rust projects (by querying their MIR) to
//! an easy-to-use format called LLBC (Low-Level Borrow Calculus), which is
//! basically MIR cleaned up and where the control-flow has been reconstructed.
//! This AST is serialized as JSON files.
//!
//!
//! We structured the project by following the approach used by [rust-clippy](https://github.com/rust-lang/rust-clippy).
//! In order to query the results of the Rustc compiler, we need to implement
//! a driver which calls Rustc while giving it some callbacks.
//! The problem is that finding the proper arguments to call Rustc with can
//! be difficult. For instance, provided the project we want to analyse with
//! Charon has already been built (and in particular its dependencies), it is
//! very difficult to provide the proper `--extern` arguments, indicating
//! where to find the compiled external dependencies. For instance, even if
//! we look in the `target` folder, the compiled depedencies are decorated
//! with a hash, and we don't know where this hash comes from.
//! Computing those arguments is, however, Cargo's responsability. As a
//! consequence, we follow Clippy's approach by piggy-backing on Cargo.  We
//! call Cargo as if we were building the project, but set up the environment
//! variable `RUSTC_WORKSPACE_WRAPPER` so that Cargo calls `charon-driver`
//! instead of Rustc upon building the target project. More specifically:
//! Cargo will call Rustc to build the dependencies, *then* will call
//! charon-driver with the arguments it would have given to Rustc to build
//! the target project.
//! Upon being called, charon-driver (see `charon_driver`) will simply call
//! Rustc with the arguments it was provided (and a few minor modifications).
//! Also, in order to transmit options from cargo-charon (this file)
//! to charon-driver (`charon-driver`), we serialize those options and store
//! them in a specific environment variable, so that charon-driver can
//! deserialize them later and use them to guide the extraction in the
//! callbacks.

#![cfg_attr(feature = "deny-warnings", deny(warnings))]

// Don't link with the `charon_lib` crate so that the `charon` binary doesn't have to dynamically
// link to `librustc_driver.so` etc.
mod cli_options;
mod logger;

use clap::Parser;
use cli_options::{CliOpts, CHARON_ARGS};
use serde::Deserialize;
use std::env;
use std::path::PathBuf;
use std::process::Command;

// Store the toolchain details directly in the binary.
static PINNED_TOOLCHAIN: &str = include_str!("../rust-toolchain");

/// This struct is used to deserialize the "rust-toolchain" file.
#[derive(Deserialize)]
struct ToolchainFile {
    toolchain: Toolchain,
}

#[derive(Deserialize)]
struct Toolchain {
    channel: String,
    #[allow(dead_code)]
    // FIXME: ensure the right components are installed.
    components: Vec<String>,
}

fn get_pinned_toolchain() -> Toolchain {
    let file_contents: ToolchainFile = toml::from_str(PINNED_TOOLCHAIN).unwrap();
    file_contents.toolchain
}

pub fn main() {
    // Initialize the logger
    logger::initialize_logger();

    // Parse the command-line
    let options = CliOpts::parse();
    trace!("Arguments: {:?}", std::env::args());

    // Check that the options are meaningful
    assert!(
        !options.lib || options.bin.is_none(),
        "Can't use --lib and --bin at the same time"
    );

    assert!(
        !options.mir_promoted || !options.mir_optimized,
        "Can't use --mir_promoted and --mir_optimized at the same time"
    );

    assert!(
        !options.abort_on_error || !options.errors_as_warnings,
        "Can't use --abort-on-error and --errors-as-warnings at the same time"
    );

    if let Err(code) = process(&options) {
        std::process::exit(code);
    }
}

fn driver_path() -> PathBuf {
    let mut path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("charon-driver");

    if cfg!(windows) {
        path.set_extension("exe");
    }

    path
}

fn process(options: &CliOpts) -> Result<(), i32> {
    let toolchain = get_pinned_toolchain();
    let driver_path = driver_path();
    // FIXME: when using rustup, ensure the toolchain has the right components installed.
    let use_rustup = which::which("rustup").is_ok();
    // This is set by the nix develop environment and the nix builder; in both cases the toolchain
    // is set up in `$PATH` and the driver should be correctly dynamically linked.
    let correct_toolchain_is_in_path = env::var("CHARON_TOOLCHAIN_IS_IN_PATH").is_ok();

    if !use_rustup && !correct_toolchain_is_in_path {
        panic!(
            "Can't find `rustup`; please install it with your system package manager \
            or from https://rustup.rs . \
            If you are using nix, make sure to be in the flake-defined environment \
            using `nix develop`.",
        )
    }

    let exit_status = if options.no_cargo {
        // Run just the driver.
        let mut cmd;
        if correct_toolchain_is_in_path {
            trace!("We appear to have been built with nix; the driver should be correctly linked.");
            cmd = Command::new(driver_path);
        } else {
            assert!(use_rustup); // Otherwise we panicked earlier.
            trace!("Calling the driver via `rustup`");
            // If rustup is there, use it to set up the right library paths so that `charon-driver`
            // can run correctly.
            cmd = Command::new("rustup");
            cmd.arg("run");
            cmd.arg(toolchain.channel);
            cmd.arg(driver_path);
        }

        cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());
        // The driver expects the first arg to be "rustc" because that's how cargo calls it.
        cmd.arg("rustc");
        if let Some(input_file) = &options.input_file {
            cmd.arg(input_file);
        }

        // The opt-level is set by default by cargo; some tests need it.
        cmd.arg("-Copt-level=3");

        cmd.spawn()
            .expect("could not run charon-driver")
            .wait()
            .expect("failed to wait for charon-driver?")
    } else {
        let mut cmd;
        if correct_toolchain_is_in_path {
            trace!("Using nix-provided toolchain");
            cmd = Command::new("cargo");
        } else {
            assert!(use_rustup); // Otherwise we panicked earlier.
            trace!("Using rustup-provided `cargo`.");
            cmd = Command::new("rustup");
            cmd.arg("run");
            cmd.arg(toolchain.channel);
            cmd.arg("cargo");
        }

        cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());
        // Tell cargo to use the driver for all the crates in the workspace. There's no option for
        // "run only on the selected crate" so the driver might be called on a crate dependency
        // within the workspace. The driver will detect that case and run rustc normally then.
        cmd.env("RUSTC_WORKSPACE_WRAPPER", driver_path);
        // Tell the driver that we're being called by cargo.
        cmd.env("CHARON_USING_CARGO", "1");
        // Make sure we don't inherit this variable from the outside. Cargo sets this itself.
        cmd.env_remove("CARGO_PRIMARY_PACKAGE");

        // Compute the arguments of the command to call cargo
        //let cargo_subcommand = "build";
        let cargo_subcommand = "rustc";
        cmd.arg(cargo_subcommand);

        if options.lib {
            cmd.arg("--lib");
        }

        if options.bin.is_some() {
            cmd.arg("--bin");
            cmd.arg(options.bin.as_ref().unwrap().clone());
        }

        // Always compile in release mode: in effect, we want to analyze the released
        // code. Also, rustc inserts a lot of dynamic checks in debug mode, that we
        // have to clean.
        cmd.arg("--release");

        cmd.spawn()
            .expect("could not run cargo")
            .wait()
            .expect("failed to wait for cargo?")
    };

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
