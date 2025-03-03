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

use anyhow::bail;
use clap::Parser;
use options::{CliOpts, CHARON_ARGS};
use serde::Deserialize;
use std::env;
use std::ffi::OsStr;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitStatus;

use charon_lib::logger;
use charon_lib::options;
use charon_lib::trace;

mod toml_config;

// Store the toolchain details directly in the binary.
static PINNED_TOOLCHAIN: &str = include_str!("../../../rust-toolchain");

/// This struct is used to deserialize the "rust-toolchain" file.
#[derive(Deserialize)]
struct ToolchainFile {
    toolchain: Toolchain,
}

#[derive(Deserialize)]
struct Toolchain {
    channel: String,
    components: Vec<String>,
}

impl Toolchain {
    fn is_installed(&self) -> anyhow::Result<bool> {
        // FIXME: check if the right components are installed.
        let output = self.run("echo").output()?;
        Ok(output.status.success())
    }

    fn install(&self) -> anyhow::Result<()> {
        Command::new("rustup")
            .arg("install")
            .arg(&self.channel)
            .status()?;
        for component in &self.components {
            Command::new("rustup")
                .arg("component")
                .arg("add")
                .arg("--toolchain")
                .arg(&self.channel)
                .arg(component)
                .status()?;
        }
        Ok(())
    }

    fn run(&self, program: impl AsRef<OsStr>) -> Command {
        let mut cmd = Command::new("rustup");
        cmd.arg("run");
        cmd.arg(&self.channel);
        cmd.arg(program);
        cmd
    }
}

fn get_pinned_toolchain() -> Toolchain {
    let file_contents: ToolchainFile = toml::from_str(PINNED_TOOLCHAIN).unwrap();
    file_contents.toolchain
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

/// Build a command that calls the given binary in the correct toolchain environment. This uses
/// rustup to provide the correct toolchain, unless we're in a nix context where the toolchain is
/// already in PATH.
fn in_toolchain(program: impl AsRef<OsStr>) -> anyhow::Result<Command> {
    let toolchain = get_pinned_toolchain();
    // This is set by the nix develop environment and the nix builder; in both cases the toolchain
    // is set up in `$PATH` and the driver should be correctly dynamically linked.
    let correct_toolchain_is_in_path = env::var("CHARON_TOOLCHAIN_IS_IN_PATH").is_ok();

    let cmd = if correct_toolchain_is_in_path {
        trace!("We appear to have been built with nix; using the rust toolchain in PATH.");
        Command::new(program)
    } else {
        trace!("Using rustup-provided toolchain.");
        if !toolchain.is_installed()? {
            println!("The required toolchain is not installed. Installing...");
            toolchain.install()?;
        }
        toolchain.run(program)
    };
    Ok(cmd)
}

fn driver_cmd() -> anyhow::Result<Command> {
    // We need `in_toolchain` to get the right library paths.
    let mut cmd = in_toolchain(driver_path())?;
    // The driver expects the first arg to be "rustc" because that's how cargo calls it.
    cmd.arg("rustc");
    Ok(cmd)
}

pub fn main() -> anyhow::Result<()> {
    // Initialize the logger
    logger::initialize_logger();

    // Parse the command-line
    let mut options = CliOpts::parse();
    trace!("Arguments: {:?}", std::env::args());
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

    let rustc_version =
        rustc_version::VersionMeta::for_command(driver_cmd()?).unwrap_or_else(|err| {
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
        let mut cmd = driver_cmd()?;

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
        let mut cmd = in_toolchain("cargo")?;

        if !options.only_cargo {
            // Tell cargo to use the driver for all the crates in the workspace. There's no option for
            // "run only on the selected crate" so the driver might be called on a crate dependency
            // within the workspace. The driver will detect that case and run rustc normally then.
            cmd.env("RUSTC_WORKSPACE_WRAPPER", driver_path());
            // Tell the driver that we're being called by cargo.
            cmd.env("CHARON_USING_CARGO", "1");
            // Make sure we don't inherit this variable from the outside. Cargo sets this itself.
            cmd.env_remove("CARGO_PRIMARY_PACKAGE");
        }

        cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());

        // Compute the arguments of the command to call cargo
        //let cargo_subcommand = "build";
        let cargo_subcommand = "rustc";
        cmd.arg(cargo_subcommand);

        // Make sure the build target is explicitly set. This is needed to detect which crates are
        // proc-macro/build-script in `charon-driver`.
        cmd.arg("--target");
        cmd.arg(host);

        if options.lib {
            cmd.arg("--lib");
        }

        if options.bin.is_some() {
            cmd.arg("--bin");
            cmd.arg(options.bin.as_ref().unwrap().clone());
        }

        for arg in &options.cargo_args {
            cmd.arg(arg);
        }

        cmd.spawn()
            .expect("could not run cargo")
            .wait()
            .expect("failed to wait for cargo?")
    };

    if exit_status.success() {
        Ok(())
    } else {
        let code = exit_status.code().unwrap_or(-1);
        // Rethrow the exit code
        std::process::exit(code);
    }
}
