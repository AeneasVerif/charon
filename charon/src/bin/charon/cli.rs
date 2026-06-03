use charon_lib::options::{CliOpts, SerializationFormat};
use clap::{Args, Parser, Subcommand};
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[clap(name = "Charon")]
pub struct Cli {
    #[command(subcommand)]
    pub command: Charon,
}

#[derive(Debug, Subcommand)]
pub enum Charon {
    /// Runs charon on a single rust file (and the modules it references, if any).
    Rustc(RustcArgs),
    /// Runs charon on a cargo project. If a `[package.metadata.charon]` section is present in
    /// `Cargo.toml`, options are also read from it.
    Cargo(CargoArgs),
    /// Run charon on a single ui test, which is mostly like `charon rustc` but parses special
    /// `//@` comments at the top.
    #[command(name = "ui_test", alias = "ui-test")]
    UiTest(UiTestArgs),
    /// Print the path to the rustc toolchain used by charon.
    ToolchainPath(ToolchainPathArgs),
    /// Print the rustc toolchain version used by charon.
    ToolchainVersion,
    /// Pretty-print the given llbc file.
    PrettyPrint(PrettyPrintArgs),
    /// Print the version.
    Version,
}

/// Read a llbc or ullbc file and pretty print it.
#[derive(Args, Debug)]
pub struct PrettyPrintArgs {
    /// Single file path to llbc or ullbc
    pub file: PathBuf,
    /// Serialization format of the input file.
    #[arg(long, value_enum, default_value_t)]
    pub format: SerializationFormat,
}

/// Usage: `charon cargo [charon options] -- [rustc options]`
#[derive(clap::Args, Debug)]
pub struct RustcArgs {
    #[command(flatten)]
    pub opts: CliOpts,

    /// Args that `rustc` accepts.
    #[arg(last = true)]
    pub rustc: Vec<String>,
}

/// Usage: `charon cargo [charon options] -- [cargo build options]`
#[derive(clap::Args, Debug)]
pub struct CargoArgs {
    #[command(flatten)]
    pub opts: CliOpts,

    /// Args that `cargo build` accepts.
    #[arg(last = true)]
    pub cargo: Vec<String>,
}

/// Usage: `charon ui_test <file.rs> [charon args]...`
#[derive(clap::Args, Debug)]
pub struct UiTestArgs {
    /// Rust UI test file to run.
    pub file: PathBuf,

    /// Extra Charon arguments to add to the generated `charon rustc` invocation.
    #[arg(allow_hyphen_values = true, trailing_var_arg = true)]
    pub args: Vec<String>,
}

/// Usage: `charon toolchain-path`
#[derive(clap::Args, Debug)]
pub struct ToolchainPathArgs {}
