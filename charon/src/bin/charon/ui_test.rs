use anyhow::{Context, Result, anyhow, bail};
use indoc::indoc as unindent;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitStatus},
};

use crate::cli::UiTestArgs;

enum OutputKind {
    PrettyLlbc,
    RunWithMiniRust,
}

enum ExpectedResult {
    Success,
    KnownFailure,
    KnownPanic,
    KnownUb,
}

struct MagicComments {
    output: OutputKind,
    expected: ExpectedResult,
    ignore_warnings: bool,
    ignore: bool,
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
    - `//@ output=run-with-minirust`: run the program in MiniRust and record its stdout;
    - `//@ known-failure`: a test that is expected to fail.
    - `//@ known-panic`: a test that is expected to panic.
    - `//@ known-ub`: a MiniRust test that is expected to encounter undefined behavior.
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

    A test can be run several times with different options using revisions:
    - `//@ revisions=<rev1>,<rev2>,...`: declare the revisions; each is a separate test, with
         output stored in `<file>.<rev>.out`.
    - `//@[<rev>] <comment>`: a comment that only applies to revision `<rev>`.
    "
);

pub fn run(args: UiTestArgs) -> Result<ExitStatus> {
    let magic_comments = parse_magic_comments(&args.file, args.revision.as_deref())?;
    if magic_comments.ignore {
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
        let mut cmd = Command::new(std::env::current_exe()?);
        let status = cmd
            .arg("rustc")
            .arg("--no-serialize")
            .arg("--")
            .arg("--crate-type=rlib")
            .arg(format!("--crate-name={crate_name}"))
            .arg("-o")
            .arg(rlib_path)
            .arg(rs_path)
            // The main test crate consumes this as an extern dependency, so unlike regular
            // `charon rustc` invocations we need rustc to leave the `.rlib` behind.
            .env("CHARON_EMIT_ARTIFACTS", "1")
            .status()?;
        if !status.success() {
            bail!("failed to compile auxiliary crate `{crate_name}` with status {status}");
        }
    }

    // Run Charon.
    let mut cmd = Command::new(std::env::current_exe()?);
    cmd.arg("rustc");

    // Charon args.
    let run_with_minirust = matches!(magic_comments.output, OutputKind::RunWithMiniRust);
    if !run_with_minirust {
        cmd.arg("--print-llbc");
    }
    if magic_comments.default_options && !run_with_minirust {
        cmd.arg("--preset=tests");
    }
    if !magic_comments.ignore_warnings {
        cmd.arg("--error-on-warnings");
    }
    if run_with_minirust {
        cmd.args([
            "--run-with-minirust",
            "--no-serialize",
            "--start-from=crate::main",
        ]);
    } else if !matches!(magic_comments.expected, ExpectedResult::Success) {
        cmd.arg("--no-serialize");
    } else {
        cmd.arg("--dest-file");
        let file_name = args
            .file
            .with_extension(args.revision.as_deref().unwrap_or_default());
        cmd.arg(file_name); // extension will be added by format=all
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
    let expected_code = match magic_comments.expected {
        ExpectedResult::Success => return Ok(status),
        ExpectedResult::KnownFailure => {
            let failed_compilation = if run_with_minirust {
                matches!(status.code(), Some(1 | 2))
            } else {
                !status.success() && status.code() != Some(101)
            };
            if failed_compilation {
                return Ok(ExitStatus::default());
            }
            "failed compilation"
        }
        ExpectedResult::KnownPanic => {
            if status.code() == Some(if run_with_minirust { 3 } else { 101 }) {
                return Ok(ExitStatus::default());
            }
            "a panic"
        }
        ExpectedResult::KnownUb => {
            if status.code() == Some(4) {
                return Ok(ExitStatus::default());
            }
            "undefined behavior"
        }
    };
    bail!("expected {expected_code}, but `charon rustc` exited with status {status}")
}

fn parse_magic_comments(input_path: &Path, revision: Option<&str>) -> Result<MagicComments> {
    // Parse the magic comments.
    let mut comments = MagicComments {
        output: OutputKind::PrettyLlbc,
        expected: ExpectedResult::Success,
        ignore_warnings: false,
        ignore: false,
        charon_opts: Vec::new(),
        rustc_opts: Vec::new(),
        default_options: true,
        auxiliary_crates: Vec::new(),
    };
    let mut revisions: Option<Vec<&str>> = None;
    let contents = fs::read_to_string(input_path)?;
    for line in contents.lines() {
        let Some(line) = line.strip_prefix("//@") else {
            break;
        };
        let mut line = line.trim();
        // `//@[rev] comment` only applies to revision `rev`.
        if let Some((rev, rest)) = line.strip_prefix('[').and_then(|l| l.split_once(']')) {
            if revisions.as_ref().is_none_or(|revs| !revs.contains(&rev)) {
                bail!("`//@[{rev}]` refers to an undeclared revision");
            }
            if revision != Some(rev) {
                continue;
            }
            line = rest.trim();
        }
        if let Some(revs) = line.strip_prefix("revisions=") {
            let split_revisions: Vec<_> = revs.split(',').map(str::trim).collect();
            if revisions.is_some() {
                bail!("`//@ revisions` may only be given once");
            }
            if revision.is_none_or(|rev| !split_revisions.contains(&rev)) {
                bail!("`--revision` must be passed with one of the revisions {split_revisions:?}");
            }
            revisions = Some(split_revisions);
        } else if line == "known-panic" {
            comments.expected = ExpectedResult::KnownPanic;
        } else if line == "known-failure" {
            comments.expected = ExpectedResult::KnownFailure;
        } else if line == "known-ub" {
            comments.expected = ExpectedResult::KnownUb;
        } else if line == "ignore-warnings" {
            comments.ignore_warnings = true;
        } else if line == "output=pretty-llbc" {
            comments.output = OutputKind::PrettyLlbc;
        } else if line == "output=run-with-minirust" {
            comments.output = OutputKind::RunWithMiniRust;
        } else if line == "ignore" || line == "skip" {
            comments.ignore = true;
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
    if revisions.is_none() && revision.is_some() {
        bail!("`--revision` was passed but the test has no revisions");
    }
    if matches!(comments.expected, ExpectedResult::KnownUb)
        && !matches!(comments.output, OutputKind::RunWithMiniRust)
    {
        bail!("`known-ub` requires `output=run-with-minirust`");
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
