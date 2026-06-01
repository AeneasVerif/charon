//! Ui tests for the charon compiler. Each `<file>.rs` file in `ui/` is passed to `charon ui_test`,
//! which parses special comments and runs Charon. The corresponding pretty-printed llbc output
//! will be stored in `<file>.out`, and CI will ensure these stay up-to-date.
use anyhow::{Context, Result, bail};
use assert_cmd::prelude::CommandCargoExt;
use libtest_mimic::Trial;
use regex::Regex;
use snapbox::filter::Filter as _;
use std::{
    error::Error,
    fs::read_to_string,
    path::{Path, PathBuf},
    process::Command,
    sync::LazyLock,
};
use walkdir::{DirEntry, WalkDir};

use util::compare_or_overwrite;
mod util;

static TESTS_DIR: &str = "tests/ui";

enum OutputStream {
    Stdout,
    Stderr,
}

struct MagicComments {
    ignore: bool,
    output_stream: OutputStream,
    /// Whether we should store the test output in a file and check it.
    check_output: bool,
}

fn parse_magic_comments(input_path: &Path) -> Result<MagicComments> {
    // Parse the magic comments.
    let mut comments = MagicComments {
        ignore: false,
        output_stream: OutputStream::Stdout,
        check_output: true,
    };
    for line in read_to_string(input_path)?.lines() {
        let Some(line) = line.strip_prefix("//@") else {
            break;
        };
        let line = line.trim();
        if line == "ignore" || line == "skip" {
            comments.ignore = true;
        } else if line == "no-check-output" {
            comments.check_output = false;
        } else if line == "known-panic" || line == "known-failure" {
            comments.output_stream = OutputStream::Stderr;
        }
    }
    Ok(comments)
}

struct Case {
    input_path: PathBuf,
    expected: PathBuf,
    magic_comments: MagicComments,
}

fn setup_test(input_path: PathBuf) -> Result<Trial> {
    let name = input_path
        .to_str()
        .context("test path is not valid UTF-8")?
        .strip_prefix(TESTS_DIR)
        .context("test path is not under the tests/ui directory")?
        .strip_prefix("/")
        .context("test path is the tests/ui directory itself")?
        .to_owned();
    let expected = input_path.with_extension("out");
    let magic_comments = parse_magic_comments(&input_path)?;
    let ignore = magic_comments.ignore;
    let case = Case {
        input_path,
        expected,
        magic_comments,
    };
    let trial = Trial::test(name, move || perform_test(&case).map_err(|err| err.into()))
        .with_ignored_flag(ignore);
    Ok(trial)
}

fn perform_test(test_case: &Case) -> Result<()> {
    let mut cmd = Command::cargo_bin("charon")?;
    cmd.arg("ui_test");
    cmd.arg(&test_case.input_path);
    let cmd_str = format!("charon ui_test {}", test_case.input_path.display());

    let output = cmd.output()?;
    let stderr = String::from_utf8(output.stderr.clone())?;
    let stdout = String::from_utf8(output.stdout.clone())?;

    // Hide thread id from the output.
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"thread '(\w+)' \(\d+\) (panicked|has overflowed)").unwrap());
    let stderr = RE.replace_all(&stderr, "thread '$1' $2");

    if !output.status.success() {
        if !stdout.is_empty() {
            // Write output file anyway to make debugging easier.
            let actual = snapbox::Data::text(stdout);
            let actual = snapbox::filter::FilterNewlines.filter(actual);
            actual.write_to_path(&test_case.expected)?;
        }
        bail!("Command: `{cmd_str}`\nCompilation failed:\n{stderr}")
    }
    let test_output = match test_case.magic_comments.output_stream {
        OutputStream::Stdout => stdout.as_str(),
        OutputStream::Stderr => stderr.as_ref(),
    };
    if test_case.magic_comments.check_output {
        compare_or_overwrite(test_output, &test_case.expected)?;
    } else {
        // Remove the `out` file if there's one from a previous run.
        if test_case.expected.exists() {
            std::fs::remove_file(&test_case.expected)?;
        }
    }

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
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
            Result::Ok(test)
        })
        .collect::<Result<_>>()?;

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run(&args, tests).exit()
}
