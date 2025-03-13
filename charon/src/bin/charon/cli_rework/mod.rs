use charon_lib::options::CliOpts;
use clap::{Args, Parser, Subcommand};
use std::path::PathBuf;

/// `charon cargo`
mod cargo;

#[derive(Debug, Parser)]
#[clap(name = "Charon")]
struct Cli {
    // Makes CliOpts parsable.
    // This should be removed once subcommands are fully implemented.
    #[command(flatten)]
    opts: CliOpts,

    #[command(subcommand)]
    command: Option<Charon>,
}

#[derive(Debug, Subcommand)]
enum Charon {
    PrettyPrint(PrettyPrintArgs),
    Cargo(cargo::CargoArgs),
}

/// Read a llbc or ullbc file and pretty print it.
#[derive(Args, Debug)]
struct PrettyPrintArgs {
    /// Single file path to llbc or ullbc
    file: PathBuf,
}

/// The meaning of return value:
/// * Ok(None) => Early exit since charon is done
/// * Ok(Some(_)) => Back to original logics before subcommands are implemented
/// * Err(_) => Early exit due to error
pub fn run() -> anyhow::Result<Option<CliOpts>> {
    let cli = Cli::parse();

    match cli.command {
        Some(Charon::PrettyPrint(pretty_print)) => {
            let krate = charon_lib::deserialize_llbc(&pretty_print.file)?;
            println!("{krate}");
            return Ok(None);
        }
        Some(Charon::Cargo(subcmd_cargo)) => {
            let mut options = subcmd_cargo.opts;
            options.cargo_args = subcmd_cargo.cargo;
            Ok(Some(options))
        }
        _ => Ok(Some(cli.opts)),
    }
}
