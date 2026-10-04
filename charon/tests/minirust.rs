//! Run MiniRust's `minimize` UI suite.
use anyhow::{Context, Result, bail};
use assert_cmd::prelude::CommandCargoExt;
use itertools::Itertools;
use libtest_mimic::Trial;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::Duration,
};
use wait_timeout::ChildExt;
use walkdir::WalkDir;

const TIMEOUT: Duration = Duration::from_secs(60);

// Known failures
const FAILURES: &[(&str, &[&str])] = &[
    // Known charon limitations
    (
        "MiniRust output does not support unions because we lack padding information",
        &[
            "pass/size_of_val.rs",
            "pass/stdlib_mir.rs",
            "pass/str.rs",
            "pass/union.rs",
            "ub/enum_mark_used_bytes.rs",
            "ub/ptr_byte_order_matters.rs",
        ],
    ),
    (
        "unable to translate caller_location to MiniRust",
        &[
            "pass/catch_unwind.rs",
            "pass/ops.rs",
            "pass/ptr.rs",
            "pass/slice.rs",
            "pass/tree_borrows/cell_lazy_write_to_surrounding.rs",
            "pass/tree_borrows/cell_inside_slice_lazy_write_to_surrounding.rs",
            "pass/tree_borrows/zero_sized_cell_lazy_write_to_surrounding.rs",
            "ub/assume.rs",
            "ub/ptr_offset_from_unsigned.rs",
            "ub/ptr_offset_not_multiple.rs",
            "ub/slice_dangling.rs",
        ],
    ),
    // Unexpected translation bugs
    (
        "missing marker-trait information for this type",
        &["pass/closure.rs", "pass/closure_iterator_combinator.rs"],
    ),
    (
        "Relocation: invalid global name",
        &[
            "pass/casts.rs",
            "pass/const.rs",
            "pass/const_gap.rs",
            "pass/nullary_op.rs",
            "pass/overflow.rs",
            "pass/scalar_tuple.rs",
            "pass/small_arrays.rs",
            "pass/tree_borrows/tree_borrows.rs",
            "pass/tree_borrows/protector_end_access_special_cases.rs",
            "ub/tree_borrows/protector/protector_end_write.rs",
        ],
    ),
    // Unexpected runtime bugs
    ("has overflowed its stack", &["pass/static.rs"]),
    (
        "got exit status: 0, stdout \"100\\n3\\n\"",
        &["pass/relocation2.rs"],
    ),
    (
        "MiniRust UB: Tree Borrows: local write of Frozen reference",
        &["pass/atomic.rs"],
    ),
    (
        "MiniRust UB: reached unreachable code",
        &["panic/catch_unwind_abort.rs", "panic/struct_abort.rs"],
    ),
];

#[derive(Clone, Copy)]
enum Outcome {
    Pass,
    Panic,
    Ub,
}

impl Outcome {
    fn exit_code(self) -> i32 {
        match self {
            Self::Pass => 0,
            Self::Panic => 3,
            Self::Ub => 4,
        }
    }
}

struct Case {
    name: String,
    source: PathBuf,
    flags: Vec<String>,
    ignore: bool,
    stdout: PathBuf,
    stderr: PathBuf,
    outcome: Outcome,
}

fn gather_cases(path: PathBuf, name: &str, outcome: Outcome) -> Result<Vec<Case>> {
    let contents = fs::read_to_string(&path)?;
    let directives: Vec<_> = contents
        .lines()
        .map_while(|line| line.strip_prefix("//@"))
        .map(str::trim)
        .collect();
    let revisions = directives
        .iter()
        .find_map(|line| line.strip_prefix("revisions:"))
        .map(|names| names.split_whitespace().map(Some).collect_vec())
        .unwrap_or_else(|| vec![None]);

    revisions
        .into_iter()
        .map(|revision| {
            let mut flags = Vec::new();
            let mut ignore = false;
            for directive in &directives {
                let directive = if let Some((name, rest)) = directive
                    .strip_prefix('[')
                    .and_then(|line| line.split_once(']'))
                {
                    if revision != Some(name) {
                        continue;
                    }
                    rest.trim()
                } else {
                    directive
                };
                if let Some(args) = directive.strip_prefix("compile-flags:") {
                    for arg in args.split_whitespace() {
                        match arg {
                            // Charon always uses Tree Borrows.
                            "--minirust-tree-borrows" => {}
                            _ if arg.starts_with("--minirust-") => {
                                ignore = true;
                            }
                            _ => flags.push(arg.to_owned()),
                        }
                    }
                }
            }
            if let Some(revision) = revision {
                flags.push(format!("--cfg={revision}"));
            }
            let output_file = |extension: &str| {
                let extension = if let Some(revision) = revision {
                    &format!("{}.{extension}", revision)
                } else {
                    extension
                };
                path.with_extension(extension)
            };
            Ok(Case {
                name: match revision {
                    Some(revision) => format!("{name}#{revision}"),
                    None => name.to_owned(),
                },
                source: path.clone(),
                flags,
                ignore,
                stdout: output_file("stdout"),
                stderr: output_file("stderr"),
                outcome,
            })
        })
        .collect()
}

fn expected_output(path: &Path) -> Result<String> {
    if path.exists() {
        fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))
    } else {
        Ok(String::new())
    }
}

fn run_case(case: &Case, intrinsics_crate: &Path) -> Result<()> {
    let mut child = Command::cargo_bin("charon")?
        .args([
            "rustc",
            "--run-with-minirust",
            "--no-serialize",
            "--start-from=crate::main",
            "--",
        ])
        .arg(&case.source)
        .args([
            "--crate-name=test_crate",
            "--crate-type=rlib",
            "--edition=2021",
            "--cap-lints=allow",
            "--cfg=miri",
            "-Zmir-opt-level=0",
            "-Zmir-preserve-ub",
            "-Zub-checks=false",
            "-Zextra-const-ub-checks",
        ])
        .arg(format!(
            "--extern=intrinsics={}",
            intrinsics_crate.display()
        ))
        .args(&case.flags)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // Spawn readers to avoid the process blocking on a blogged pipe.
    let stdout = child.stdout.take().context("missing stdout pipe")?;
    let stderr = child.stderr.take().context("missing stderr pipe")?;
    let stdout_reader = std::thread::spawn(move || std::io::read_to_string(stdout));
    let stderr_reader = std::thread::spawn(move || std::io::read_to_string(stderr));

    let status = match child.wait_timeout(TIMEOUT)? {
        Some(status) => status,
        None => {
            child.kill()?;
            child.wait()?;
            bail!("timed out after {}s", TIMEOUT.as_secs());
        }
    };
    let stdout = stdout_reader.join().unwrap()?;
    let stderr = stderr_reader.join().unwrap()?;

    let expected_stdout = expected_output(&case.stdout)?;
    let expected_stderr = expected_output(&case.stderr)?;

    // We check that the stdout and stderr matches the expected outputs stored alongside the test
    // files. For failures, MiniRust and Charon use different diagnostic wording, so we compare
    // only output preceding the MiniRust diagnostic.
    if status.code() != Some(case.outcome.exit_code()) || stdout != expected_stdout {
        bail!(
            "expected exit {} and stdout {expected_stdout:?}; got {status}, stdout {stdout:?}, stderr:\n{stderr}",
            case.outcome.exit_code()
        );
    }
    let expected_stderr = match case.outcome {
        Outcome::Pass => expected_stderr.as_str(),
        Outcome::Panic | Outcome::Ub => expected_stderr.split("fatal error:").next().unwrap(),
    };
    if !stderr.starts_with(expected_stderr)
        || matches!(case.outcome, Outcome::Pass) && stderr != expected_stderr
    {
        bail!("expected stderr {expected_stderr:?}; got:\n{stderr}");
    }
    Ok(())
}

fn main() -> Result<()> {
    let temp = tempfile::tempdir()?;

    let minimize_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .context("Charon has no workspace parent")?
        .join("crates/minirust/tooling/minimize");
    let intrinsics_dir = minimize_dir.join("intrinsics");
    let tests_dir = minimize_dir.join("tests");
    if !tests_dir.is_dir() {
        bail!(
            "MiniRust's minimize suite is not available at {}",
            tests_dir.display()
        );
    }

    // Build the intrinsics crate.
    let intrinsics_rlib = {
        let intrinsics_rlib = temp.path().join("libintrinsics.rlib");
        let source = intrinsics_dir.join("src/lib.rs");
        let output = Command::cargo_bin("charon")?
            .args(["rustc", "--no-serialize", "--exclude=crate", "--"])
            .arg(&source)
            .args(["--crate-name=intrinsics", "--crate-type=rlib", "-o"])
            .arg(&intrinsics_rlib)
            .env("CHARON_EMIT_ARTIFACTS", "1")
            .output()?;
        if !output.status.success() {
            bail!(
                "could not compile MiniRust test intrinsics:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        intrinsics_rlib
    };

    let mut trials = Vec::new();
    for (subdir, outcome) in [
        ("pass", Outcome::Pass),
        ("panic", Outcome::Panic),
        ("ub", Outcome::Ub),
    ] {
        for entry in WalkDir::new(tests_dir.join(subdir)) {
            let entry = entry?;
            if entry
                .path()
                .extension()
                .is_none_or(|extension| extension != "rs")
            {
                continue;
            }
            let path = entry.into_path();
            let case_name = path
                .strip_prefix(&tests_dir)?
                .to_string_lossy()
                .replace('\\', "/");
            for case in gather_cases(path, &case_name, outcome)? {
                // Because of non-determinism, a single test may trigger different failures
                // depending on the run.
                let reasons: Vec<_> = FAILURES
                    .iter()
                    .filter(|(_, paths)| paths.iter().any(|path| case_name.starts_with(path)))
                    .map(|(reason, _)| *reason)
                    .collect();
                let ignore = case.ignore;
                let intrinsics_rlib = intrinsics_rlib.clone();
                trials.push(
                    Trial::test(case.name.clone(), move || {
                        let result: Result<()> = match run_case(&case, &intrinsics_rlib) {
                            Ok(()) if !reasons.is_empty() => Err(anyhow::anyhow!(
                                "unexpectedly passed; expected failure containing one of {reasons:?}"
                            )),
                            Err(error) if !reasons.is_empty() => {
                                let error_text = format!("{error:#}");
                                if reasons.iter().any(|reason| error_text.contains(reason)) {
                                    Ok(())
                                } else {
                                    Err(anyhow::anyhow!(
                                        "expected failure containing one of {reasons:?}; got:\n{error:#}"
                                    ))
                                }
                            }
                            result => result,
                        };
                        result.map_err(Into::into)
                    })
                    .with_ignored_flag(ignore),
                );
            }
        }
    }
    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run(&args, trials).exit()
}
