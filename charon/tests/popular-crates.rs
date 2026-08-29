//! This test downlads the `NUMBER_OF_CRATES` most downloaded crates from crates.io and runs charon
//! on each of them.
//!
//! This test requires a feature flag. To run, call `make test-popular-crates`.
#![cfg(feature = "popular-crates-test")]
mod util;

use anyhow::{Result, bail};
use assert_cmd::prelude::CommandCargoExt;
use itertools::Itertools;
use std::{
    path::Path,
    process::{Command, Stdio},
    sync::Arc,
    time::Duration,
};
use util::popular_crates::{client, extract_crate, limit_memory_usage};
use wait_timeout::ChildExt;

const NUMBER_OF_CRATES: u64 = 500;
const CRATES_PER_PAGE: u64 = 100;

/// Crates that don't `cargo build` on my machine.
static BUILD_FAILURES: &[&str] = &[
    // Errors with our pinned rustc.
    "is_terminal_polyfill",
    "mime",
    "serde_yaml",
    "tokio-native-tls",
    "try-lock",
    "unsafe-libyaml",
    "wait-timeout",
    // Requires a feature to be selected.
    "derive_more",
    "tiny-keccak",
    // Requires system library.
    "clang-sys",
    "plotters",
    "zstd-sys",
    // Intentionally emits a compile error.
    "bincode",
    // Doesn't build on Linux.
    "windows",
    "winreg",
];

/// Crates that error because of charon.
static CHARON_FAILURES: &[&str] = &[
    // See `closure-nested-dyn-ice` test.
    "rayon-core",
    // See `impossible-recursive-trait-proof` test
    "windows-core",
    // Timeout
    "cexpr",
    "generic-array",
];

fn process_crate(version: &crates_io_api::Version) -> Result<()> {
    let crate_dir = extract_crate(version)?;
    let llbc_path = {
        // Relative to the crate directory
        let mut path = Path::new("..").to_path_buf();
        path.push(crate_dir.file_name().unwrap());
        path.add_extension("llbc");
        path
    };

    // Call charon
    let mut command = Command::cargo_bin("charon")?;
    command
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .current_dir(&crate_dir)
        .env("CARGO_BUILD_JOBS", "1")
        .arg("cargo")
        // Removing either of these options hits a lot more timeouts/crashes.
        .args(["--ullbc", "--hide-marker-traits"])
        .arg("--dest-file")
        .arg(&llbc_path);
    limit_memory_usage(&mut command);
    let mut child = command.spawn()?;
    // Drain stderr while Charon runs: waiting before reading can fill the pipe buffer and deadlock
    // the child process.
    let stderr = child.stderr.take().unwrap();
    let stderr_reader = std::thread::spawn(move || std::io::read_to_string(stderr));
    let timeout = Duration::from_secs(30);
    let status_code = match child.wait_timeout(timeout)? {
        Some(status) => status,
        None => {
            child.kill()?;
            child.wait()?;
            bail!("Compilation timed out after {}s", timeout.as_secs())
        }
    };

    let stderr = stderr_reader.join().expect("stderr reader panicked")?;
    if !status_code.success() {
        bail!("Compilation failed: {stderr}")
    }

    Ok(())
}

#[test] // Only include in release mode
pub fn test_popular_crates() -> Result<()> {
    use crates_io_api::*;
    let client = Arc::new(client());

    let mut crates = Vec::new();
    for page in 1..=NUMBER_OF_CRATES.div_ceil(CRATES_PER_PAGE) {
        let q = CratesQuery::builder()
            .sort(Sort::Downloads)
            .page_size(CRATES_PER_PAGE)
            .page(page)
            .build();
        crates.extend(client.crates(q)?.crates);
    }
    crates.truncate(NUMBER_OF_CRATES as usize);

    let tests: Vec<_> = crates
        .into_iter()
        .map(|krate| {
            let known_failure = BUILD_FAILURES.contains(&krate.name.as_str())
                || CHARON_FAILURES.contains(&krate.name.as_str());
            let name = format!("{}-{}", krate.name, krate.max_version);
            let client = Arc::clone(&client);
            let test = libtest_mimic::Trial::test(name, move || {
                let krate = client.get_crate(&krate.name)?;
                let version = krate.versions.into_iter().next().unwrap();
                process_crate(&version).map_err(|err| err.into())
            })
            .with_ignored_flag(known_failure);
            Ok::<_, Error>(test)
        })
        .try_collect()?;

    let args = libtest_mimic::Arguments::from_args();
    libtest_mimic::run(&args, tests).exit()
}
