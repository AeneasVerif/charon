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
//! variable `RUSTC_WRAPPER` so that Cargo calls `charon-driver` instead of
//! Rustc upon building the target project. More specifically:
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
use anyhow::{Context, Result};
use charon_lib::{
    common::arg_value,
    export::{CrateData, multi_target},
    logger,
    options::{CHARON_ARGS, CliOpts},
};
use clap::Parser;
use cli::{Charon, Cli};
use itertools::Itertools;
use std::{env, process::ExitStatus};
use toolchain::toolchain_path;

#[macro_use]
extern crate charon_lib;

mod cli;
mod toml_config;
mod toolchain;

pub fn main() -> Result<()> {
    // Initialize the logger
    logger::initialize_logger();

    // Parse the command-line
    let cli = Cli::parse();
    let exit_status = match cli.command {
        Charon::PrettyPrint(pretty_print) => {
            let krate = charon_lib::deserialize_llbc(&pretty_print.file)?;
            println!("{krate}");
            ExitStatus::default()
        }
        Charon::Cargo(subcmd_cargo) => {
            let mut options = subcmd_cargo.opts;
            let targets = std::mem::take(&mut options.targets);
            if targets.is_empty() {
                translate_with_cargo(options, subcmd_cargo.cargo)?
            } else {
                translate_multi_target(targets, options, |opts: CliOpts, target: &str| {
                    let mut cargo_args = subcmd_cargo.cargo.clone();
                    cargo_args.extend(["--target".to_owned(), target.to_owned()]);
                    translate_with_cargo(opts, cargo_args)
                })?
            }
        }
        Charon::Rustc(mut subcmd_rustc) => {
            let mut options = subcmd_rustc.opts;
            options.rustc_args.append(&mut subcmd_rustc.rustc);
            let targets = std::mem::take(&mut options.targets);
            if targets.is_empty() {
                translate_without_cargo(options)?
            } else {
                translate_multi_target(targets, options, |mut opts: CliOpts, target: &str| {
                    opts.rustc_args
                        .extend(["--target".to_owned(), target.to_owned()]);
                    translate_without_cargo(opts)
                })?
            }
        }
        Charon::ToolchainPath(_) => {
            let path = toolchain_path()?;
            println!("{}", path.display());
            ExitStatus::default()
        }
        Charon::Version => {
            println!("{}", charon_lib::VERSION);
            ExitStatus::default()
        }
    };

    handle_exit_status(exit_status)
}

/// Run translation once per target (in parallel), then merge the results.
fn translate_multi_target(
    targets: Vec<String>,
    options: CliOpts,
    translate_one: impl Fn(CliOpts, &str) -> anyhow::Result<ExitStatus> + Sync,
) -> anyhow::Result<ExitStatus> {
    let temp_dir = tempfile::tempdir().context("failed to create temp dir")?;

    // Translate each target in its own thread.
    let krates: Vec<_> = std::thread::scope(|scope| {
        let options = &options;
        let translate_one = &translate_one;
        let temp_dir = temp_dir.path();
        let handles: Vec<_> = targets
            .iter()
            .enumerate()
            .map(|(i, target)| {
                scope.spawn(move || -> anyhow::Result<_> {
                    let mut opts = options.clone();
                    let temp_file = temp_dir.join(format!("target_{i}.json"));
                    opts.dest_file = Some(temp_file.clone());
                    // Don't recurse into multi-target.
                    opts.targets.clear();
                    // Suppress per-target printing; we'll print the merged result.
                    opts.print_ullbc = false;
                    opts.print_llbc = false;
                    // Ensure serialization so we can load the result.
                    opts.no_serialize = false;

                    let status = translate_one(opts, target)?;
                    if !status.success() {
                        eprintln!("translation for target {target} failed with status {status}");
                        handle_exit_status(status)?;
                    }

                    let krate =
                        CrateData::deserialize_from_file(&temp_file).with_context(|| {
                            format!("failed to load translation result for target {target}")
                        })?;
                    Ok(krate)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("target translation thread panicked"))
            .try_collect()
    })?;

    // Merge all crates.
    let merged = multi_target::merge(options.clone(), krates);

    if options.print_llbc || options.print_ullbc {
        println!("{}", merged.translated);
    }

    // Serialize the merged result unless --no-serialize was passed.
    if !options.no_serialize {
        let target_filename = options.target_filename(&merged.translated.crate_name);
        merged
            .serialize_to_file(&target_filename)
            .map_err(|()| anyhow::anyhow!("failed to serialize merged crate"))?;
    }

    Ok(ExitStatus::default())
}

fn translate_with_cargo(
    mut options: CliOpts,
    cargo_args: Vec<String>,
) -> anyhow::Result<ExitStatus> {
    ensure_rustup();
    if let Some(toml) = toml_config::read_toml() {
        options = toml.apply(options);
    }
    options.validate()?;
    let mut cmd = toolchain::in_toolchain("cargo")?;
    cmd.env("RUSTC_WRAPPER", toolchain::driver_path());
    cmd.env("CHARON_USING_CARGO", "1");
    cmd.env_remove("CARGO_PRIMARY_PACKAGE");
    cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());
    cmd.arg("build");
    if arg_value(&cargo_args, "--target").is_none() {
        // Make sure the build target is explicitly set. This is needed to detect which crates are
        // proc-macro/build-script in `charon-driver`.
        cmd.arg("--target");
        cmd.arg(&get_rustc_version()?.host);
    }
    cmd.args(cargo_args);
    trace!("running {cmd:?}");
    Ok(cmd
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo?"))
}

fn translate_without_cargo(mut options: CliOpts) -> anyhow::Result<ExitStatus> {
    ensure_rustup();
    options.validate()?;
    let mut cmd = toolchain::driver_cmd()?;
    let is_specified = |arg| {
        let mut iter = options.rustc_args.iter();
        iter.any(|input| input.starts_with(arg))
    };
    if !is_specified("--target") {
        // Make sure the build target is explicitly set. This is needed to detect which crates are
        // proc-macro/build-script in `charon-driver`.
        cmd.arg("--target");
        cmd.arg(&get_rustc_version()?.host);
    }
    cmd.args(std::mem::take(&mut options.rustc_args));
    cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());
    Ok(cmd
        .spawn()
        .expect("could not run charon-driver")
        .wait()
        .expect("failed to wait for charon-driver?"))
}

fn get_rustc_version() -> anyhow::Result<rustc_version::VersionMeta> {
    let cmd = toolchain::driver_cmd()?;
    let rustc_version = rustc_version::VersionMeta::for_command(cmd).unwrap_or_else(|err| {
        panic!("failed to determine underlying rustc version of Charon:\\n{err:?}",)
    });
    Ok(rustc_version)
}

fn ensure_rustup() {
    // FIXME: when using rustup, ensure the toolchain has the right components installed.
    let use_rustup = which::which("rustup").is_ok();
    // This is set by the nix develop environment and the nix builder; in both cases the toolchain
    // is set up in `\$PATH` and the driver should be correctly dynamically linked.
    let correct_toolchain_is_in_path = env::var("CHARON_TOOLCHAIN_IS_IN_PATH").is_ok();

    if !use_rustup && !correct_toolchain_is_in_path {
        panic!(
            "Can't find `rustup`; please install it with your system package manager \\
            or from https://rustup.rs . \\
            If you are using nix, make sure to be in the flake-defined environment \\
            using `nix develop`.",
        )
    }
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
