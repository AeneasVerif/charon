//! This test downlads the `NUMBER_OF_CRATES` most downloaded crates from crates.io and runs charon
//! on each of them.
//!
//! This test requires a feature flag. To run, call `make test-popular-crates`.
#![cfg(feature = "popular-crates-test")]
use anyhow::{Context, Result, bail};
use assert_cmd::prelude::CommandCargoExt;
use crates_io_api::Version;
use flate2::read::GzDecoder;
use itertools::Itertools;
use std::{
    fs::File,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::Arc,
    time::Duration,
};
use tar::Archive;
use wait_timeout::ChildExt;

static TESTS_DIR: &str = "tests/popular-crates";

const NUMBER_OF_CRATES: u64 = 500;
const CRATES_PER_PAGE: u64 = 100;

#[cfg(target_os = "linux")]
fn limit_memory_usage(command: &mut Command) {
    use std::os::unix::process::CommandExt;

    const MEMORY_LIMIT: libc::rlim_t = 4 * 1024 * 1024 * 1024;

    unsafe {
        command.pre_exec(|| {
            let limit = libc::rlimit {
                rlim_cur: MEMORY_LIMIT,
                rlim_max: MEMORY_LIMIT,
            };
            if libc::setrlimit(libc::RLIMIT_AS, &limit) == 0 {
                Ok(())
            } else {
                Err(std::io::Error::last_os_error())
            }
        });
    }
}

#[cfg(not(target_os = "linux"))]
fn limit_memory_usage(_: &mut Command) {}

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

/// Downloads and extracts the crate into a subdirectory of `TESTS_DIR` and returns the path to
/// that directory.
fn extract_crate(version: &Version) -> Result<PathBuf> {
    let full_name = &format!("{}-{}", version.crate_name, version.num);
    let download_url = format!("https://crates.io{}", version.dl_path);
    let directory = PathBuf::from(format!("{}/{}", TESTS_DIR, full_name));
    if directory.exists() {
        // Assuùe the directory already contains the extracted crate.
        return Ok(directory);
    }

    let archive_path = {
        let mut path = directory.clone();
        path.add_extension("tar.gz");
        path
    };
    {
        // Download the crate archive
        let mut temp_file = File::create(&archive_path)
            .with_context(|| format!("while creating `{}`", archive_path.display()))?;
        reqwest::blocking::get(download_url)?.copy_to(&mut temp_file)?;
    }
    {
        // Extract the crate archive
        let temp_file = File::open(&archive_path)?;
        let mut archive = Archive::new(GzDecoder::new(temp_file));
        // This assumes that the archive always contains exactly one folder named
        // `{crate_name}-{version}`, which seems to be the case. Worst case we get unexpected files
        // inside the `popular-crates` subfolder.
        archive
            .unpack(TESTS_DIR)
            .with_context(|| "while extracting archive")?;
    }
    std::fs::remove_file(archive_path)?;

    Ok(directory)
}

fn process_crate(version: &Version) -> Result<()> {
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
    let client = Arc::new(
        SyncClient::new(
            "charon-test-runner (Nadrieril@users.noreply.github.com)",
            std::time::Duration::from_millis(1000),
        )
        .unwrap(),
    );

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
