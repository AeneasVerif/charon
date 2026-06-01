use anyhow::{Context, Result, anyhow, bail};
use indoc::indoc as unindent;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitStatus},
};

use crate::{cli::UiTestArgs, toolchain};

enum TestKind {
    PrettyLlbc,
    KnownFailure,
    KnownPanic,
    IgnoreWarnings,
    Ignore,
}

struct MagicComments {
    test_kind: TestKind,
    /// The options with which to run charon.
    charon_opts: Vec<String>,
    /// The options to pass to rustc.
    rustc_opts: Vec<String>,
    /// Whether we should set some sensible default options (using --preset=test).
    default_options: bool,
    /// A list of paths to files that must be compiled as dependencies for this test.
    auxiliary_crates: Vec<PathBuf>,
}

static HELP_STRING: &str = unindent!(
    "Options are:
    - `//@ output=pretty-llbc`: record the pretty-printed llbc (default);
    - `//@ known-failure`: a test that is expected to fail.
    - `//@ known-panic`: a test that is expected to panic.
    - `//@ ignore-warnings`: a test for which warnings should be ignored (instead of erroring).
    - `//@ ignore`: skip the test.

    Other comments can be used to control the behavior of charon:
    - `//@ charon-args=<charon cli options>`
    - `//@ charon-arg=<single charon cli option>`
    - `//@ rustc-args=<rustc cli options>`
    - `//@ no-check-output`: don't store the output in a file; useful if the output is unstable or
         differs between debug and release mode.
    - `//@ no-default-options`: don't set default options like --hide-allocator
    - `//@ aux-crate=<file path>`: compile this file as a crate dependency.
    "
);

pub fn run(args: UiTestArgs) -> Result<ExitStatus> {
    let magic_comments = parse_magic_comments(&args.file)?;
    if matches!(magic_comments.test_kind, TestKind::Ignore) {
        return Ok(ExitStatus::default());
    }

    // Dependencies.
    let deps: Vec<_> = magic_comments
        .auxiliary_crates
        .iter()
        .map(|path| {
            let crate_name = path_to_crate_name(path).with_context(|| {
                format!(
                    "failed to compute auxiliary crate name for {}",
                    path.display()
                )
            })?;
            let rlib_file_name = format!("lib{crate_name}.rlib"); // yep it must start with "lib"
            let rlib_path = path
                .parent()
                .with_context(|| format!("{} has no parent directory", path.display()))?
                .join(rlib_file_name);
            Ok((crate_name, path.clone(), rlib_path))
        })
        .collect::<Result<_>>()?;
    for (crate_name, rs_path, rlib_path) in deps.iter() {
        let mut cmd = toolchain::in_toolchain("rustc")?;
        let status = cmd
            .arg("--crate-type=rlib")
            .arg("-Zalways-encode-mir")
            .arg(format!("--crate-name={crate_name}"))
            .arg("-o")
            .arg(rlib_path)
            .arg(rs_path)
            .status()?;
        if !status.success() {
            bail!("failed to compile auxiliary crate `{crate_name}` with status {status}");
        }
    }

    // Run Charon.
    let mut cmd = Command::new(std::env::current_exe()?);
    cmd.arg("rustc");

    // Charon args.
    cmd.arg("--print-llbc");
    if magic_comments.default_options {
        cmd.arg("--preset=tests");
    }
    if !matches!(magic_comments.test_kind, TestKind::IgnoreWarnings) {
        cmd.arg("--error-on-warnings");
    }
    if matches!(
        magic_comments.test_kind,
        TestKind::KnownPanic | TestKind::KnownFailure
    ) {
        cmd.arg("--no-serialize");
    } else {
        cmd.arg("--dest-file");
        cmd.arg(args.file.with_extension("")); // extension will be added by format=all
        cmd.arg("--format=all");
    }
    cmd.args(&magic_comments.charon_opts);
    cmd.args(&args.args);

    // Rustc args.
    cmd.arg("--");
    cmd.arg(&args.file);
    cmd.arg("--crate-name=test_crate");
    cmd.arg("--crate-type=rlib");
    cmd.arg("--allow=unused"); // Removes noise
    for (crate_name, _, rlib_path) in deps {
        cmd.arg(format!("--extern={crate_name}={}", rlib_path.display()));
    }
    cmd.args(&magic_comments.rustc_opts);

    let status = cmd
        .status()
        .context("failed to run `charon rustc` for ui test")?;
    let status_description = if status.success() {
        "succeeded"
    } else if status.code() == Some(101) {
        "panicked"
    } else {
        "failed"
    };
    match magic_comments.test_kind {
        TestKind::PrettyLlbc | TestKind::IgnoreWarnings => Ok(status),
        TestKind::KnownPanic if status.code() == Some(101) => Ok(ExitStatus::default()),
        TestKind::KnownPanic => {
            bail!(
                "compilation was expected to panic but instead {}",
                status_description
            )
        }
        TestKind::KnownFailure if !status.success() && status.code() != Some(101) => {
            Ok(ExitStatus::default())
        }
        TestKind::KnownFailure => {
            bail!(
                "compilation was expected to fail but instead {}",
                status_description
            )
        }
        TestKind::Ignore => unreachable!(),
    }
}

fn parse_magic_comments(input_path: &Path) -> Result<MagicComments> {
    // Parse the magic comments.
    let mut comments = MagicComments {
        test_kind: TestKind::PrettyLlbc,
        charon_opts: Vec::new(),
        rustc_opts: Vec::new(),
        default_options: true,
        auxiliary_crates: Vec::new(),
    };
    for line in fs::read_to_string(input_path)?.lines() {
        let Some(line) = line.strip_prefix("//@") else {
            break;
        };
        let line = line.trim();
        if line == "known-panic" {
            comments.test_kind = TestKind::KnownPanic;
        } else if line == "known-failure" {
            comments.test_kind = TestKind::KnownFailure;
        } else if line == "ignore-warnings" {
            comments.test_kind = TestKind::IgnoreWarnings;
        } else if line == "output=pretty-llbc" {
            comments.test_kind = TestKind::PrettyLlbc;
        } else if line == "ignore" || line == "skip" {
            comments.test_kind = TestKind::Ignore;
        } else if line == "no-default-options" {
            comments.default_options = false;
        } else if line == "no-check-output" {
            // Output comparison is managed by `tests/ui.rs`.
        } else if let Some(charon_opts) = line.strip_prefix("charon-args=") {
            comments
                .charon_opts
                .extend(charon_opts.split_whitespace().map(str::to_owned));
        } else if let Some(charon_opt) = line.strip_prefix("charon-arg=") {
            comments.charon_opts.push(charon_opt.to_owned());
        } else if let Some(rustc_opts) = line.strip_prefix("rustc-args=") {
            comments
                .rustc_opts
                .extend(rustc_opts.split_whitespace().map(str::to_owned));
        } else if let Some(crate_path) = line.strip_prefix("aux-crate=") {
            let crate_path: PathBuf = crate_path.into();
            let parent = input_path
                .parent()
                .with_context(|| format!("{} has no parent directory", input_path.display()))?;
            comments.auxiliary_crates.push(parent.join(crate_path));
        } else {
            return Err(
                anyhow!("Unknown magic comment: `{line}`. {HELP_STRING}").context(format!(
                    "While processing file {}",
                    input_path.to_string_lossy()
                )),
            );
        }
    }
    Ok(comments)
}

fn path_to_crate_name(path: &Path) -> Option<String> {
    Some(
        path.file_name()?
            .to_str()?
            .strip_suffix(".rs")?
            .replace(['-'], "_"),
    )
}
