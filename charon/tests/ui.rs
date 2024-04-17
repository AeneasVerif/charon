//! Ui tests for the charon compiler. Each `<file>.rs` file in `ui/` will be passed to the charon
//! driver. The corresponding pretty-printed llbc output will be stored in `<file>.llbc`, and CI
//! will ensure these stay up-to-date.
//!
//! Files can start with special comments that affect the test behavior. Supported magic comments:
//! see [`HELP_STRING`].
use anyhow::{anyhow, bail};
use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
use indoc::indoc as unindent;
use libtest_mimic::{Outcome, Test};
use std::{
    error::Error,
    fs::read_to_string,
    path::{Path, PathBuf},
    process::Command,
};
use walkdir::{DirEntry, WalkDir};

use charon_lib::cli_options::{CliOpts, CHARON_ARGS};

static TESTS_DIR: &str = "tests/ui";

enum TestKind {
    PrettyLlbc,
    KnownFailure,
    KnownPanic,
    Skip,
}

struct MagicComments {
    test_kind: TestKind,
    /// The options with which to run charon.
    cli_opts: CliOpts,
    /// Whether we should store the test output in a file and check it.
    check_output: bool,
    /// A list of paths to files that must be compiled as dependencies for this test.
    auxiliary_crates: Vec<PathBuf>,
}

static HELP_STRING: &str = unindent!(
    "Options are:
    - `//@ output=pretty-llbc`: record the pretty-printed llbc (default);
    - `//@ known-failure`: a test that is expected to fail.
    - `//@ known-panic`: a test that is expected to panic.
    - `//@ skip`: skip the test.
    
    Other comments can be used to control the behavior of charon:
    - `//@ charon-args=<charon cli options>`
    - `//@ no-check-output`: don't store the output in a file; useful if the output is unstable or
         differs between debug and release mode.
    - `//@ aux-crate=<file path>`: compile this file as a crate dependency.
    "
);

fn parse_magic_comments(input_path: &std::path::Path) -> anyhow::Result<MagicComments> {
    // Parse the magic comments.
    let mut comments = MagicComments {
        test_kind: TestKind::PrettyLlbc,
        cli_opts: CliOpts::default(),
        check_output: true,
        auxiliary_crates: Vec::new(),
    };
    for line in read_to_string(input_path)?.lines() {
        let Some(line) = line.strip_prefix("//@") else { break };
        let line = line.trim();
        if line == "known-panic" {
            comments.test_kind = TestKind::KnownPanic;
        } else if line == "known-failure" {
            comments.test_kind = TestKind::KnownFailure;
        } else if line == "output=pretty-llbc" {
            comments.test_kind = TestKind::PrettyLlbc;
        } else if line == "skip" {
            comments.test_kind = TestKind::Skip;
        } else if line == "no-check-output" {
            comments.check_output = false;
        } else if let Some(charon_opts) = line.strip_prefix("charon-args=") {
            use clap::Parser;
            // The first arg is normally the command name.
            let args = ["dummy"].into_iter().chain(charon_opts.split_whitespace());
            comments.cli_opts.update_from(args);
        } else if let Some(crate_path) = line.strip_prefix("aux-crate=") {
            let crate_path: PathBuf = crate_path.into();
            let crate_path = input_path.parent().unwrap().join(crate_path);
            comments.auxiliary_crates.push(crate_path)
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

struct Case {
    input_path: PathBuf,
    expected: PathBuf,
    magic_comments: MagicComments,
}

fn setup_test(input_path: PathBuf) -> anyhow::Result<Test<Case>> {
    let name = input_path
        .to_str()
        .unwrap()
        .strip_prefix(TESTS_DIR)
        .unwrap()
        .strip_prefix("/")
        .unwrap()
        .to_owned();
    let expected = input_path.with_extension("out");
    let magic_comments = parse_magic_comments(&input_path)?;
    Ok(Test {
        name: name.clone(),
        kind: "".into(),
        is_ignored: matches!(magic_comments.test_kind, TestKind::Skip),
        is_bench: false,
        data: Case {
            input_path,
            expected,
            magic_comments,
        },
    })
}

#[derive(Clone, Copy)]
enum Action {
    Verify,
    Overwrite,
}

fn path_to_crate_name(path: &Path) -> Option<String> {
    Some(
        path.file_name()?
            .to_str()?
            .strip_suffix(".rs")?
            .replace(['-'], "_"),
    )
}

fn perform_test(test_case: &Case, action: Action) -> anyhow::Result<()> {
    // Dependencies
    // Vec of (crate name, path to crate.rs, path to libcrate.rlib).
    let deps: Vec<(String, PathBuf, String)> = test_case
        .magic_comments
        .auxiliary_crates
        .iter()
        .cloned()
        .map(|path| {
            let crate_name = path_to_crate_name(&path).unwrap();
            let rlib_file_name = format!("lib{crate_name}.rlib"); // yep it must start with "lib"
            let rlib_path = path.parent().unwrap().join(rlib_file_name);
            let rlib_path = rlib_path.to_str().unwrap().to_owned();
            (crate_name, path, rlib_path)
        })
        .collect();
    for (crate_name, rs_path, rlib_path) in deps.iter() {
        Command::new("rustc")
            .arg("--crate-type=rlib")
            .arg(format!("--crate-name={crate_name}"))
            .arg("-o")
            .arg(rlib_path)
            .arg(rs_path)
            .output()?
            .assert()
            .try_success()
            .map_err(|e| anyhow!(e.to_string()))?;
    }

    // Call the charon driver.
    let mut options = test_case.magic_comments.cli_opts.clone();
    options.print_llbc = true;
    options.no_serialize = true;
    options.crate_name = Some("test_crate".into());

    let mut cmd = Command::cargo_bin("charon-driver")?;
    cmd.env(CHARON_ARGS, serde_json::to_string(&options).unwrap());
    cmd.arg("rustc");
    cmd.arg(test_case.input_path.to_string_lossy().into_owned());
    cmd.arg("--edition=2021"); // To avoid needing `extern crate`
    for (crate_name, _, rlib_path) in deps {
        cmd.arg(format!("--extern={crate_name}={rlib_path}"));
    }
    let output = cmd.output()?;
    let stderr = String::from_utf8(output.stderr.clone())?;

    match test_case.magic_comments.test_kind {
        TestKind::KnownPanic => {
            if output.status.code() != Some(101) {
                let status = if output.status.success() {
                    "succeeded"
                } else {
                    "errored"
                };
                bail!("Compilation was expected to panic but instead {status}: {stderr}");
            }
        }
        TestKind::KnownFailure => {
            if output.status.code() != Some(1) {
                let status = if output.status.success() {
                    "succeeded"
                } else {
                    "panicked"
                };
                bail!("Compilation was expected to fail but instead {status}: {stderr}");
            }
        }
        TestKind::PrettyLlbc => {
            if !output.status.success() {
                bail!("Compilation failed: {stderr}")
            }
        }
        TestKind::Skip => unreachable!(),
    }
    if test_case.magic_comments.check_output {
        let actual = snapbox::Data::text(stderr).map_text(snapbox::utils::normalize_lines);
        match action {
            Action::Verify => expect_file_contents(&test_case.expected, actual)?,
            Action::Overwrite => actual.write_to(&test_case.expected)?,
        }
    } else {
        // Remove the `out` file if there's one from a previous run.
        if test_case.expected.exists() {
            std::fs::remove_file(&test_case.expected)?;
        }
    }

    Ok(())
}

/// Compare the file contents with the provided string and error ith a diff if they differ.
fn expect_file_contents(path: &Path, actual: snapbox::Data) -> snapbox::Result<()> {
    let expected = snapbox::Data::read_from(path, Some(snapbox::DataFormat::Text))?
        .map_text(snapbox::utils::normalize_lines);

    if expected != actual {
        let mut buf = String::new();
        let palette = snapbox::report::Palette::auto();
        snapbox::report::write_diff(
            &mut buf,
            &expected,
            &actual,
            Some(&path.display()),
            Some(&"charon output"),
            palette,
        )
        .map_err(|e| e.to_string())?;
        Err(buf.into())
    } else {
        Ok(())
    }
}

#[test]
fn ui() -> Result<(), Box<dyn Error>> {
    let action = if std::env::var("IN_CI").as_deref() == Ok("1") {
        Action::Verify
    } else {
        Action::Overwrite
    };

    let root: PathBuf = TESTS_DIR.into();
    let file_filter = |e: &DirEntry| e.file_name().to_str().is_some_and(|s| s.ends_with(".rs"));
    let tests: Vec<_> = WalkDir::new(root)
        .min_depth(1)
        .into_iter()
        .filter_map(|entry| match entry {
            Ok(entry) if !file_filter(&entry) => None,
            res => Some(res),
        })
        .map(|entry| {
            let entry = entry?;
            let test = setup_test(entry.into_path())?;
            anyhow::Result::Ok(test)
        })
        .collect::<anyhow::Result<_>>()?;

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run_tests(&args, tests, move |t| match perform_test(&t.data, action) {
        Ok(()) => Outcome::Passed,
        Err(err) => Outcome::Failed {
            msg: Some(err.to_string()),
        },
    })
    .exit()
}
