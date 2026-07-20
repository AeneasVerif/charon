//! Tests for running charon with cargo. Cases are set up by hand; this aims to test cargo-specific
//! shenanigans such as dependencies.
use anyhow::{Context, bail, ensure};
use assert_cmd::prelude::CommandCargoExt;
use charon_lib::{ast::FileName, export::CrateData, options::SerializationFormat};
use itertools::Itertools;
use libtest_mimic::Trial;
use regex::Regex;
use std::{error::Error, ffi::OsStr, path::PathBuf, process::Command, sync::LazyLock};

use util::compare_or_overwrite;
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
    /// Extra arguments to pass to cargo.
    cargo_args: Vec<String>,
}

fn perform_test(test_case: &Case) -> anyhow::Result<()> {
    // Clean the cargo cache to avoid caching issues.
    Command::new("cargo")
        .arg("clean")
        .current_dir(&test_case.dir)
        .status()?;
    // Call charon
    let mut cmd = Command::cargo_bin("charon")?;
    cmd.current_dir(&test_case.dir);
    cmd.arg("cargo");
    cmd.arg("--error-on-warnings");
    cmd.arg("--print-llbc");
    if matches!(test_case.expect, Failure) {
        cmd.arg("--no-serialize");
    }
    cmd.arg("--dest-file");
    cmd.arg(test_case.output_file.with_extension("llbc"));
    cmd.args(&test_case.charon_args);
    cmd.arg("--");
    cmd.args(&test_case.cargo_args);
    if matches!(test_case.expect, Failure) {
        cmd.arg("--quiet");
    }

    let cmd_str = format!(
        "charon {}",
        cmd.get_args().map(OsStr::to_string_lossy).join(" ")
    );
    let output = cmd.output()?;

    let success = output.status.success();
    let output = if success {
        output.stdout
    } else {
        output.stderr
    };
    let output = String::from_utf8(output.clone())?;
    // Hide thread id from the output.
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"thread '(\w+)' \(\d+\) (panicked|has overflowed)").unwrap());
    let output = RE.replace_all(&output, "thread '$1' $2");
    // Hide rlib paths from the output.
    static RE2: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"extern location (.*) does not exist:.*\.rlib").unwrap());
    let mut output = RE2
        .replace_all(&output, "extern location $1 does not exist")
        .to_string();
    match test_case.expect {
        Success if !success => bail!("Command: `{cmd_str}`\nCompilation failed: {output}"),
        Failure if success => {
            bail!("Command: `{cmd_str}`\nCompilation succeeded but shouldn't have: {output}")
        }
        Failure if !success => {
            // Hack to avoid differences between CI and local tests.
            let current_dir = std::env::current_dir()?;
            let current_dir = current_dir.to_string_lossy();
            output = output
                .lines()
                .filter(|line| {
                    !line
                        .trim_start()
                        .starts_with("process didn't exit successfully")
                })
                .map(|line| line.replace(&*current_dir, "."))
                .join("\n");
        }
        _ => {}
    }
    compare_or_overwrite(output, &test_case.output_file)?;

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let root: PathBuf = PathBuf::from(TESTS_DIR).canonicalize()?;
    let mktest = |name: &str,
                  dir: PathBuf,
                  charon_args: &[String],
                  cargo_args: &[String],
                  expect: Expect| {
        let charon_args = charon_args.to_vec();
        let cargo_args = cargo_args.to_vec();
        let output_file = root.join(format!("{name}.out"));
        Trial::test(name, move || {
            let case = Case {
                dir,
                output_file,
                expect,
                charon_args,
                cargo_args,
            };
            perform_test(&case).map_err(|err| err.into())
        })
    };
    let issue_1298 = {
        let name = "issue-1298-absolute-path-for-generated-files";
        let dir = root.join(name);
        let output_file = root.join(format!("{name}.out"));
        Trial::test(name, move || {
            let result: anyhow::Result<()> = (|| {
                let case = Case {
                    dir,
                    output_file: output_file.clone(),
                    expect: Success,
                    charon_args: vec![],
                    cargo_args: vec![],
                };
                perform_test(&case)?;

                // Issue #1298: a file generated under OUT_DIR should be recorded
                // relative to the crate directory.
                let crate_data = CrateData::deserialize_from_file(
                    &output_file.with_extension("llbc"),
                    SerializationFormat::Json,
                )?;
                let generated_file = crate_data
                    .translated
                    .files
                    .iter()
                    .find(|file| match &file.name {
                        FileName::Local(path) => {
                            path.file_name() == Some(OsStr::new("generated.rs"))
                        }
                        _ => false,
                    })
                    .with_context(|| {
                        let paths = crate_data
                            .translated
                            .files
                            .iter()
                            .map(|file| file.name.to_string())
                            .join(", ");
                        format!("could not find generated.rs in translated files: {paths}")
                    })?;
                let FileName::Local(path) = &generated_file.name else {
                    unreachable!();
                };
                ensure!(
                    !path.is_absolute(),
                    "expected generated.rs to be recorded as a relative path, got {}",
                    path.display()
                );
                ensure!(
                    path.starts_with("target"),
                    "expected generated.rs to be recorded relative to the crate directory, got {}",
                    path.display()
                );
                Ok(())
            })();
            result.map_err(|err| err.into())
        })
    };
    let tests = vec![
        mktest("build-script", root.join("build-script"), &[], &[], Success),
        mktest(
            "dependencies",
            root.join("dependencies"),
            &[],
            &["--features=test_feature".to_owned()],
            Success,
        ),
        mktest(
            "private-dependency",
            root.join("private-dependency"),
            &["--include-referenced=dependency".to_owned()],
            &[],
            Success,
        ),
        mktest(
            "error-dependencies",
            root.join("error-dependencies"),
            &[],
            &[],
            Failure,
        ),
        mktest("toml", root.join("toml"), &[], &[], Success),
        mktest("unsafe_", root.join("unsafe_"), &[], &[], Success),
        mktest(
            "workspace",
            root.join("workspace"),
            &["--extract-opaque-bodies".to_owned()],
            &["--package=crate2".to_owned()],
            Success,
        ),
        mktest(
            "issue-396-lib-bin",
            root.join("issue-396-lib-bin"),
            &[],
            &[],
            Success,
        ),
        mktest(
            "issue-412-dup-deps",
            root.join("issue-412-dup-deps"),
            &["--include=mydup".to_owned()],
            &[],
            Success,
        ),
        mktest(
            "multi-targets",
            root.join("multi-targets"),
            &[
                "--targets=i686-unknown-linux-gnu,x86_64-apple-darwin,riscv64gc-unknown-none-elf"
                    .to_owned(),
            ],
            &[],
            Success,
        ),
        issue_1298,
    ];

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run(&args, tests).exit()
}
