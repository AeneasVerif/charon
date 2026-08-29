use anyhow::{Context, Result};
use crates_io_api::{SyncClient, Version};
use flate2::read::GzDecoder;
use std::{fs::File, path::PathBuf, process::Command, time::Duration};
use tar::Archive;

pub const TESTS_DIR: &str = "tests/popular-crates";

pub fn client() -> SyncClient {
    SyncClient::new(
        "charon-test-runner (Nadrieril@users.noreply.github.com)",
        Duration::from_millis(1000),
    )
    .unwrap()
}

/// Downloads and extracts the crate into a subdirectory of [`TESTS_DIR`] and returns the path to
/// that directory.
pub fn extract_crate(version: &Version) -> Result<PathBuf> {
    let full_name = &format!("{}-{}", version.crate_name, version.num);
    let download_url = format!("https://crates.io{}", version.dl_path);
    let directory = PathBuf::from(format!("{TESTS_DIR}/{full_name}"));
    if directory.exists() {
        // Assume the directory already contains the extracted crate.
        return Ok(directory);
    }

    let archive_path = {
        let mut path = directory.clone();
        path.add_extension("tar.gz");
        path
    };
    {
        let mut temp_file = File::create(&archive_path)
            .with_context(|| format!("while creating `{}`", archive_path.display()))?;
        reqwest::blocking::get(download_url)?.copy_to(&mut temp_file)?;
    }
    {
        let temp_file = File::open(&archive_path)?;
        let mut archive = Archive::new(GzDecoder::new(temp_file));
        // Crate archives contain one folder named `{crate_name}-{version}`.
        archive
            .unpack(TESTS_DIR)
            .context("while extracting archive")?;
    }
    std::fs::remove_file(archive_path)?;

    Ok(directory)
}

#[cfg(target_os = "linux")]
pub fn limit_memory_usage(command: &mut Command) {
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
pub fn limit_memory_usage(_: &mut Command) {}
