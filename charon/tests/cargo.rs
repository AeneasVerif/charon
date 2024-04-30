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
}

fn perform_test(test_case: &Case, action: Action) -> anyhow::Result<()> {
    // Call charon
    let mut cmd = Command::cargo_bin("charon")?;
    cmd.current_dir(&test_case.dir);
    cmd.arg("--print-llbc");
    cmd.arg("--no-serialize");
    let output = cmd.output()?;

    let stderr = String::from_utf8(output.stderr.clone())?;
    if output.status.success() {
        compare_or_overwrite(action, stderr, &test_case.expected)?;
    } else {
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
    let tests = vec![Test {
        name: "dependencies".to_owned(),
        kind: "".into(),
        is_ignored: false,
        is_bench: false,
        data: Case {
            dir: root.join("dependencies"),
            expected: root.join("dependencies.out"),
        },
    }];

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run_tests(&args, tests, move |t| match perform_test(&t.data, action) {
        Ok(()) => Outcome::Passed,
        Err(err) => Outcome::Failed {
            msg: Some(err.to_string()),
        },
    })
    .exit()
}
