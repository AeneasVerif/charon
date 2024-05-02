//! Tests for running charon with cargo. Cases are set up by hand; this aims to test cargo-specific
//! shenanigans such as dependencies.
use anyhow::bail;
use assert_cmd::prelude::CommandCargoExt;
use libtest_mimic::{Outcome, Test};
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
    cmd.arg(test_case.expected.canonicalize()?.with_extension("llbc"));
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

#[test]
fn cargo() -> Result<(), Box<dyn Error>> {
    let action = if std::env::var("IN_CI").as_deref() == Ok("1") {
        Action::Verify
    } else {
        Action::Overwrite
    };

    let root: PathBuf = TESTS_DIR.into();
    let mktest = |name: &str, dir: PathBuf, charon_args: &[String]| Test {
        name: name.to_owned(),
        kind: "".into(),
        is_ignored: false,
        is_bench: false,
        data: Case {
            dir,
            expected: root.join(format!("{name}.out")),
            charon_args: charon_args.to_vec(),
        },
    };
    let tests = vec![
        mktest("dependencies", root.join("dependencies"), &[]),
        mktest(
            "workspace",
            root.join("workspace").join("crate2"),
            &["--extract-opaque-bodies".to_owned()],
        ),
    ];

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run_tests(&args, tests, move |t| match perform_test(&t.data, action) {
        Ok(()) => Outcome::Passed,
        Err(err) => Outcome::Failed {
            msg: Some(err.to_string()),
        },
    })
    .exit()
}
