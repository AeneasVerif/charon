use charon_lib::options::CliOpts;

/// Usage: `charon cargo [charon options] -- [rustc options]`
#[derive(clap::Args, Debug)]
pub struct RustcArgs {
    #[command(flatten)]
    pub opts: CliOpts,

    /// Args that `rustc` accepts.
    #[arg(last = true)]
    pub rustc: Vec<String>,
}
