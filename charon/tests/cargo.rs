//! Tests for running charon with cargo. Cases are set up by hand; this aims to test cargo-specific
//! shenanigans such as dependencies.
use anyhow::bail;
use assert_cmd::prelude::CommandCargoExt;
use libtest_mimic::Trial;
use std::{error::Error, path::PathBuf, process::Command};

use util::{compare_or_overwrite, Action};

mod util;

static TESTS_DIR: &str = "tests/cargo";

struct Case {
    /// Directory to run `charon` in.
    dir: PathBuf,
    /// Path of the output pretty-llbc file.
    expected: PathBuf,
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
    cmd.arg("--print-llbc");
    cmd.arg("--dest-file");
    cmd.arg(test_case.expected.with_extension("llbc"));
    for arg in &test_case.charon_args {
        cmd.arg(arg);
    }
    let output = cmd.output()?;

    if output.status.success() {
        let stdout = String::from_utf8(output.stdout.clone())?;
        compare_or_overwrite(action, stdout, &test_case.expected)?;
    } else {
        let stderr = String::from_utf8(output.stderr.clone())?;
        bail!("Compilation failed: {stderr}")
    }

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let action = if std::env::var("IN_CI").as_deref() == Ok("1") {
        Action::Verify
    } else {
        Action::Overwrite
    };

    let root: PathBuf = PathBuf::from(TESTS_DIR).canonicalize()?;
    let mktest = |name: &str, dir: PathBuf, charon_args: &[String]| {
        let charon_args = charon_args.to_vec();
        let expected = root.join(format!("{name}.out"));
        Trial::test(name, move || {
            let case = Case {
                dir,
                expected,
                charon_args,
            };
            perform_test(&case, action).map_err(|err| err.into())
        })
    };
    let tests = vec![
        mktest("build-script", root.join("build-script"), &[]),
        mktest(
            "dependencies",
            root.join("dependencies"),
            &["--cargo-arg=--features=test_feature".to_owned()],
        ),
        mktest("toml", root.join("toml"), &[]),
        mktest(
            "workspace",
            root.join("workspace").join("crate2"),
            &["--extract-opaque-bodies".to_owned()],
        ),
    ];

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run(&args, tests).exit()
}
