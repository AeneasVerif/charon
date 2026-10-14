use anyhow::{Context, Result};
use serde::Deserialize;
use std::{env, ffi::OsStr, path::PathBuf, process::Command};

// Store the toolchain details directly in the binary.
static PINNED_TOOLCHAIN: &str = include_str!("../../../rust-toolchain");

/// This struct is used to deserialize the "rust-toolchain" file.
#[derive(Deserialize)]
struct ToolchainFile {
    toolchain: Toolchain,
}

#[derive(Deserialize)]
pub struct Toolchain {
    channel: String,
    components: Vec<String>,
}

impl Toolchain {
    fn is_installed(&self) -> Result<bool> {
        // FIXME: check if the right components are installed.
        let output = self.run("rustc").arg("--version").output()?;
        Ok(output.status.success())
    }

    fn install(&self) -> Result<()> {
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

        // Add rust driver dll to `PATH` in rustup.
        // cc
        // * https://github.com/AeneasVerif/charon/issues/588
        // * https://github.com/rust-lang/rustup/issues/3825
        if cfg!(windows) {
            cmd.env("RUSTUP_WINDOWS_PATH_ADD_BIN", "1");
        }

        cmd
    }
}

fn get_pinned_toolchain() -> Toolchain {
    let file_contents: ToolchainFile = toml::from_str(PINNED_TOOLCHAIN).unwrap();
    file_contents.toolchain
}

pub fn toolchain_version() -> String {
    get_pinned_toolchain().channel
}

pub fn driver_path() -> PathBuf {
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
pub fn in_toolchain(program: impl AsRef<OsStr>) -> Result<Command> {
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

pub fn driver_cmd() -> Result<Command> {
    // We need `in_toolchain` to get the right library paths.
    let mut cmd = in_toolchain(driver_path())?;
    // The driver expects the first arg to be "rustc" because that's how cargo calls it.
    cmd.arg("rustc");
    Ok(cmd)
}

/// Get the path to the sysroot, where the `cargo` and `rustc` binaries can be found. Prefer using
/// [`in_toolchain`] instead of this as much as possible.
pub fn toolchain_path() -> Result<PathBuf> {
    let output = in_toolchain("rustc")?.arg("--print=sysroot").output()?;
    let stdout = String::from_utf8(output.stdout)
        .with_context(|| "the output of `rustc --print=sysroot` is not UTF8 encoded".to_string())?;
    Ok(PathBuf::from(stdout.trim_end()))
}

/// The environment variable through which `charon` tells `charon-driver` which full-MIR sysroot to
/// use, if any.
pub const CHARON_SYSROOT_VAR: &str = "CHARON_RESOLVED_MIRI_SYSROOT";

/// Whether this sysroot provides libraries for the given target.
fn sysroot_has_target(sysroot: &std::path::Path, target: &str) -> bool {
    sysroot.join("lib").join("rustlib").join(target).is_dir()
}

/// Where we tell `cargo miri setup` to build the sysroot for the current toolchain.
/// We use a per-toolchain directory because Miri's default cache directory (`~/.cache/miri`) is
/// shared across all toolchains and gets overwritten when switching between Charon versions.
fn miri_sysroot_cache_dir() -> Option<PathBuf> {
    let toolchain = toolchain_version();
    let cache_dir = match env::var_os("CHARON_CACHE_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => env::home_dir()?.join(".cache").join("charon"),
    };
    Some(cache_dir.join("miri-sysroot").join(toolchain))
}

/// `cargo miri setup` sets up a sysroot containing a standard library built with
/// `-Zalways-encode-mir`.
pub fn setup_miri_sysroot(target: &str) -> Option<PathBuf> {
    if let Some(root) = env::var_os("CHARON_MIRI_SYSROOTS")
        && let sysroot = PathBuf::from(root)
        && sysroot_has_target(&sysroot, target)
    {
        return Some(sysroot);
    }

    let cache_sysroot = miri_sysroot_cache_dir();
    if let Some(sysroot) = &cache_sysroot
        && sysroot_has_target(sysroot, target)
    {
        return Some(sysroot.clone());
    }

    let mut cmd = match in_toolchain("cargo") {
        Ok(cmd) => cmd,
        Err(err) => {
            eprintln!(
                "warning: failed to find `cargo` to run `cargo miri setup` for target `{target}`; \
                falling back to rustc's default sysroot: {err}"
            );
            return None;
        }
    };
    cmd.arg("miri")
        .arg("setup")
        .arg(format!("--target={target}"))
        .arg("--print-sysroot")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("RUSTC_WRAPPER");
    if let Some(sysroot) = &cache_sysroot {
        cmd.env("MIRI_SYSROOT", sysroot);
    }

    let output = match cmd.output() {
        Ok(output) => output,
        Err(err) => {
            eprintln!(
                "warning: failed to run `cargo miri setup` for target `{target}`; \
                falling back to rustc's default sysroot: {err}"
            );
            return None;
        }
    };

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprintln!(
            "warning: `cargo miri setup` failed for target `{target}`; \
            falling back to rustc's default sysroot: {}",
            stderr.trim()
        );
        return None;
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let sysroot = stdout.lines().map(str::trim).find(|line| !line.is_empty());
    match sysroot {
        Some(sysroot) => Some(PathBuf::from(sysroot)),
        None => {
            eprintln!(
                "warning: `cargo miri setup --print-sysroot` printed no sysroot for target \
                `{target}`; falling back to rustc's default sysroot"
            );
            None
        }
    }
}
