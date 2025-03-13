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
#![feature(register_tool)]
// For when we use charon on itself
#![register_tool(charon)]

use anyhow::Result;
use charon_lib::{logger, options::CHARON_ARGS};
use std::{env, process::ExitStatus};

#[macro_use]
extern crate anyhow;
#[macro_use]
extern crate charon_lib;

/// Rename this module once subcommand migration finishes.
mod cli_rework;
mod toml_config;
mod toolchain;

pub fn main() -> Result<()> {
    // Initialize the logger
    logger::initialize_logger();

    // Parse the command-line
    trace!("Arguments: {:?}", env::args());

    let mut options = match cli_rework::run()? {
        Some(options) => options,
        None => return Ok(()),
    };

    // ******* Old cli args parsing *******
    options.validate();

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

    let cmd = toolchain::driver_cmd()?;
    let rustc_version = rustc_version::VersionMeta::for_command(cmd).unwrap_or_else(|err| {
        panic!("failed to determine underlying rustc version of Charon:\n{err:?}",)
    });
    let host = &rustc_version.host;

    let exit_status = if let Some(llbc_file) = options.read_llbc {
        let krate = charon_lib::deserialize_llbc(&llbc_file)?;
        println!("{krate}");
        ExitStatus::default()
    } else if options.no_cargo {
        if !options.cargo_args.is_empty() {
            bail!("Option `--cargo-arg` is not compatible with `--no-cargo`")
        }

        // Run just the driver.
        let mut cmd = toolchain::driver_cmd()?;

        for arg in std::mem::take(&mut options.rustc_args) {
            cmd.arg(arg);
        }

        cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());

        // Make sure the build target is explicitly set. This is needed to detect which crates are
        // proc-macro/build-script in `charon-driver`.
        cmd.arg("--target");
        cmd.arg(host);

        if let Some(input_file) = &options.input_file {
            cmd.arg(input_file);
        }

        cmd.spawn()
            .expect("could not run charon-driver")
            .wait()
            .expect("failed to wait for charon-driver?")
    } else {
        if let Some(toml) = toml_config::read_toml() {
            options = toml.apply(options);
            options.validate();
        }
        let mut cmd = toolchain::in_toolchain("cargo")?;

        // Tell cargo to use the driver for all the crates in the workspace. There's no option for
        // "run only on the selected crate" so the driver might be called on a crate dependency
        // within the workspace. The driver will detect that case and run rustc normally then.
        cmd.env("RUSTC_WORKSPACE_WRAPPER", toolchain::driver_path());
        // Tell the driver that we're being called by cargo.
        cmd.env("CHARON_USING_CARGO", "1");
        // Make sure we don't inherit this variable from the outside. Cargo sets this itself.
        cmd.env_remove("CARGO_PRIMARY_PACKAGE");

        cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());

        // Compute the arguments of the command to call cargo
        cmd.arg("build");

        // Detect if an arg if specified in cargo_args, like in `-- arg` or `--cargo-args=arg`.
        let is_specified = |arg| {
            let mut iter = options.cargo_args.iter();
            iter.any(|input| input.starts_with(arg))
        };

        // Don't set target if `-- --target` is specified by user.
        if !is_specified("--target") {
            // Make sure the build target is explicitly set. This is needed to detect which crates are
            // proc-macro/build-script in `charon-driver`.
            cmd.arg("--target");
            cmd.arg(host);
        }

        if !is_specified("--lib") && options.lib {
            cmd.arg("--lib");
        }

        if !is_specified("--bin") {
            if let Some(bin) = &options.bin {
                cmd.arg("--bin");
                cmd.arg(bin);
            }
        }

        cmd.args(options.cargo_args);

        cmd.spawn()
            .expect("could not run cargo")
            .wait()
            .expect("failed to wait for cargo?")
    };

    handle_exit_status(exit_status)
}

fn handle_exit_status(exit_status: ExitStatus) -> Result<()> {
    if exit_status.success() {
        Ok(())
    } else {
        let code = exit_status.code().unwrap_or(-1);
        // Rethrow the exit code
        std::process::exit(code);
    }
}
