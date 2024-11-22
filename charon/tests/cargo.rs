//! Tests for running charon with cargo. Cases are set up by hand; this aims to test cargo-specific
//! shenanigans such as dependencies.
use anyhow::bail;
use assert_cmd::prelude::CommandCargoExt;
use libtest_mimic::Trial;
use std::{error::Error, path::PathBuf, process::Command};

use util::{compare_or_overwrite, Action};

mod util;

static TESTS_DIR: &str = "tests/cargo";

use Expect::*;
enum Expect {
    Success,
    Failure,
}

struct Case {
    /// Directory to run `charon` in.
    dir: PathBuf,
    /// Path of the output pretty-llbc file.
    output_file: PathBuf,
    /// Should charon succeed or fail?
    expect: Expect,
    /// Extra arguments to pass to charon.
    charon_args: Vec<String>,
}

fn perform_test(test_case: &Case, action: Action) -> anyhow::Result<()> {
    // Clean the cargo cache to avoid caching issues.
    Command::new("cargo")
        .arg("clean")
        .current_dir(&test_case.dir)
        .status()?;
    // Call charon
    let mut cmd = Command::cargo_bin("charon")?;
    cmd.current_dir(&test_case.dir);
    cmd.arg("--error-on-warnings");
    cmd.arg("--print-llbc");
    if matches!(test_case.expect, Failure) {
        cmd.arg("--cargo-arg=--quiet");
    }
    cmd.arg("--dest-file");
    cmd.arg(test_case.output_file.with_extension("llbc"));
    for arg in &test_case.charon_args {
        cmd.arg(arg);
    }
    let output = cmd.output()?;

    let success = output.status.success();
    let output = if success {
        output.stdout
    } else {
        output.stderr
    };
    let output = String::from_utf8(output.clone())?;
    match test_case.expect {
        Success if !success => bail!("Compilation failed: {output}"),
        Failure if success => bail!("Compilation succeeded but shouldn't have: {output}"),
        _ => {}
    }
    compare_or_overwrite(action, output, &test_case.output_file)?;

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let action = if std::env::var("IN_CI").as_deref() == Ok("1") {
        Action::Verify
    } else {
        Action::Overwrite
    };

    let root: PathBuf = PathBuf::from(TESTS_DIR).canonicalize()?;
    let mktest = |name: &str, dir: PathBuf, charon_args: &[String], expect: Expect| {
        let charon_args = charon_args.to_vec();
        let output_file = root.join(format!("{name}.out"));
        Trial::test(name, move || {
            let case = Case {
                dir,
                output_file,
                expect,
                charon_args,
            };
            perform_test(&case, action).map_err(|err| err.into())
        })
    };
    let tests = vec![
        mktest("build-script", root.join("build-script"), &[], Success),
        mktest(
            "dependencies",
            root.join("dependencies"),
            &["--cargo-arg=--features=test_feature".to_owned()],
            Success,
        ),
        mktest(
            "error-dependencies",
            root.join("error-dependencies"),
            &[],
            Failure,
        ),
        mktest("toml", root.join("toml"), &[], Success),
        mktest(
            "workspace",
            root.join("workspace"),
            &[
                "--cargo-arg=--package=crate2".to_owned(),
                "--extract-opaque-bodies".to_owned(),
            ],
            Success,
        ),
    ];

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run(&args, tests).exit()
}
