use charon_lib::options::CliOpts;

/// Usage: `charon cargo [charon options] -- [cargo build options]`
#[derive(clap::Args, Debug)]
pub struct CargoArgs {
    #[command(flatten)]
    pub opts: CliOpts,

    /// Args that `cargo build` accepts.
    #[arg(last = true)]
    pub cargo: Vec<String>,
}
