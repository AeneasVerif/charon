use charon_lib::options::CliOpts;
use clap::{Args, Parser, Subcommand};
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[clap(name = "Charon")]
pub struct Cli {
    // Makes CliOpts parsable.
    // This should be removed once subcommands are fully implemented.
    #[command(flatten)]
    pub opts: CliOpts,

    #[command(subcommand)]
    pub command: Option<Charon>,
}

#[derive(Debug, Subcommand)]
pub enum Charon {
    PrettyPrint(PrettyPrintArgs),
}

/// Read a llbc or ullbc file and pretty print it.
#[derive(Args, Debug)]
pub struct PrettyPrintArgs {
    /// Single file path to llbc or ullbc
    pub file: PathBuf,
}
