//! Ui tests for the charon compiler. Each `<file>.rs` file in `ui/` will be passed to the charon
//! driver. The corresponding pretty-printed llbc output will be stored in `<file>.llbc`, and CI
//! will ensure these stay up-to-date.
//!
//! Files can start with special comments that affect the test behavior. Supported magic comments:
//! see [`HELP_STRING`].
use anyhow::bail;
use assert_cmd::prelude::CommandCargoExt;
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
    Unspecified,
}

struct MagicComments {
    test_kind: TestKind,
    cli_opts: CliOpts,
}

static HELP_STRING: &str = unindent!(
    "Test must start with a magic comment that determines its kind. Options are:
    - `//@ output=pretty-llbc`: record the pretty-printed llbc;
    - `//@ known-failure`: a test that is expected to fail.
    - `//@ known-panic`: a test that is expected to panic.
    
    Other comments can be used to control the behavior of charon:
    - `//@ charon-args=<charon cli options>`
    "
);

fn parse_magic_comments(input_path: &std::path::Path) -> anyhow::Result<MagicComments> {
    // Parse the magic comments.
    let mut comments = MagicComments {
        test_kind: TestKind::Unspecified,
        cli_opts: CliOpts::default(),
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
        } else if let Some(charon_opts) = line.strip_prefix("charon-args=") {
            use clap::Parser;
            // The first arg is normally the command name.
            let args = ["dummy"].into_iter().chain(charon_opts.split_whitespace());
            comments.cli_opts.update_from(args);
        } else {
            bail!(HELP_STRING);
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
        is_ignored: false,
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

fn perform_test(test_case: &Case, action: Action) -> anyhow::Result<()> {
    if matches!(test_case.magic_comments.test_kind, TestKind::Unspecified) {
        bail!(HELP_STRING);
    }

    // Call the charon driver.
    let mut options = test_case.magic_comments.cli_opts.clone();
    options.print_llbc = true;
    options.no_serialize = true;
    options.crate_name = Some("test_crate".into());

    let output = Command::cargo_bin("charon-driver")?
        .arg("rustc")
        .arg(test_case.input_path.to_string_lossy().into_owned())
        .env(CHARON_ARGS, serde_json::to_string(&options).unwrap())
        .output()?;
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
            // We don't commit the panic message to a file because it can differ between debug and
            // release modes.
            return Ok(());
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
        TestKind::Unspecified => unreachable!(),
    }
    let actual = snapbox::Data::text(stderr).map_text(snapbox::utils::normalize_lines);
    match action {
        Action::Verify => expect_file_contents(&test_case.expected, actual)?,
        Action::Overwrite => actual.write_to(&test_case.expected)?,
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
