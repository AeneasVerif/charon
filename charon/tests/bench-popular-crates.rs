//! Benchmark Charon on a small, fixed selection of popular crates.
//!
//! Each crate is translated three times. The averaged timing report is written to
//! `tests/popular-crates/bench-results.csv`.
//!
//! This test requires a feature flag. To run, call `make bench-popular-crates`.
#![cfg(feature = "popular-crates-test")]
mod util;

use anyhow::{Context, Result, bail};
use assert_cmd::prelude::CommandCargoExt;
use crates_io_api::{SyncClient, Version};
use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufWriter, Write},
    path::Path,
    process::{Command, Stdio},
    time::Duration,
};
use util::popular_crates::{client, extract_crate, limit_memory_usage};
use wait_timeout::ChildExt;

const RUNS: usize = 3;
const OUTPUT_FILE: &str = "tests/popular-crates/bench-results.csv";
const CRATES: &[(&str, &str)] = &[
    ("serde", "1.0.228"),
    ("serde_json", "1.0.142"),
    ("regex", "1.11.1"),
    ("syn", "2.0.104"),
    ("clap", "4.5.43"),
    ("tokio", "1.47.1"),
];

#[derive(Default)]
struct Timing {
    total_ms: f64,
    self_ms: f64,
    calls: f64,
}

fn find_version(client: &SyncClient, name: &str, number: &str) -> Result<Version> {
    client
        .get_crate(name)
        .with_context(|| format!("while fetching crate `{name}`"))?
        .versions
        .into_iter()
        .find(|version| version.num == number)
        .with_context(|| format!("could not find `{name}` version `{number}`"))
}

fn run_charon(version: &Version, run: usize) -> Result<Vec<(String, Timing)>> {
    let crate_dir = extract_crate(version)?;
    let llbc_path = Path::new("..").join(format!("{}-{}.llbc", version.crate_name, version.num));
    let timings_dir = tempfile::tempdir()?;
    let timings_file = timings_dir.path().join("timings.csv");

    eprintln!(
        "Benchmarking {} {} ({run}/{RUNS})",
        version.crate_name, version.num
    );
    let mut command = Command::cargo_bin("charon")?;
    command
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .current_dir(&crate_dir)
        .env("CARGO_BUILD_JOBS", "1")
        .env("CHARON_TIMINGS", &timings_file)
        .arg("cargo")
        .args(["--ullbc", "--hide-marker-traits"])
        .arg("--dest-file")
        .arg(llbc_path);
    limit_memory_usage(&mut command);

    let mut child = command.spawn()?;
    let stderr = child.stderr.take().unwrap();
    let stderr_reader = std::thread::spawn(move || std::io::read_to_string(stderr));
    let timeout = Duration::from_secs(120);
    let status = match child.wait_timeout(timeout)? {
        Some(status) => status,
        None => {
            child.kill()?;
            child.wait()?;
            bail!("Compilation timed out after {}s", timeout.as_secs())
        }
    };
    let stderr = stderr_reader.join().expect("stderr reader panicked")?;
    if !status.success() {
        bail!("Compilation failed: {stderr}")
    }

    let contents = std::fs::read_to_string(timings_file)?;
    let timings = contents
        .lines()
        .map(|line| {
            // The timing format is `crate,scope,total_ms,self_ms,calls`. Splitting numeric fields
            // from the right keeps this correct even if a scope name contains a comma.
            let (prefix, calls) = line.rsplit_once(',').context("missing call count")?;
            let (prefix, self_ms) = prefix.rsplit_once(',').context("missing self time")?;
            let (prefix, total_ms) = prefix.rsplit_once(',').context("missing total time")?;
            let (_, scope) = prefix.split_once(',').context("missing crate name")?;
            Ok((
                scope.to_owned(),
                Timing {
                    total_ms: total_ms.parse()?,
                    self_ms: self_ms.parse()?,
                    calls: calls.parse()?,
                },
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    if timings.is_empty() {
        bail!("Charon emitted no timing data")
    }
    Ok(timings)
}

#[test]
fn bench_popular_crates() -> Result<()> {
    let client = client();
    let mut output = BufWriter::new(File::create(OUTPUT_FILE)?);
    writeln!(output, "crate,scope,total_ms,self_ms,calls")?;

    for &(name, number) in CRATES {
        let version = find_version(&client, name, number)?;
        let mut timings: BTreeMap<String, Timing> = BTreeMap::new();
        for run in 1..=RUNS {
            for (scope, timing) in run_charon(&version, run)
                .with_context(|| format!("while benchmarking `{name}` version `{number}`"))?
            {
                let average = timings.entry(scope).or_default();
                average.total_ms += timing.total_ms / RUNS as f64;
                average.self_ms += timing.self_ms / RUNS as f64;
                average.calls += timing.calls / RUNS as f64;
            }
        }

        let crate_name = format!("{name}-{number}");
        for (scope, timing) in timings {
            let scope = if scope.contains([',', '"', '\n']) {
                format!("\"{}\"", scope.replace('"', "\"\""))
            } else {
                scope
            };
            writeln!(
                output,
                "{},{},{:.3},{:.3},{:.3}",
                crate_name, scope, timing.total_ms, timing.self_ms, timing.calls,
            )?;
        }
    }
    output.flush()?;
    eprintln!("Benchmark results written to {OUTPUT_FILE}");
    Ok(())
}
