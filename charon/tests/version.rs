//! Detect breaking changes to the llbc format. We commit the output of charon run on an example
//! file, and if this file changes we make sure the version of charon also changed. This is
//! best-effort, it will have false positives and negatives.
use assert_cmd::prelude::CommandCargoExt;
use serde::Deserialize;
use serde_json::Value;
use std::collections::HashMap;
use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(PartialEq, Deserialize)]
struct CrateData {
    charon_version: String,
    #[serde(flatten)]
    rest: HashMap<String, Value>,
}

fn read_crate_data(path: &Path) -> anyhow::Result<CrateData> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let crate_data: CrateData = serde_json::from_reader(reader)?;
    Ok(crate_data)
}

#[test]
fn check_version() -> anyhow::Result<()> {
    let input_file: PathBuf = "tests/version/example.rs".into();
    let output_file = input_file.with_extension("out");

    // Call charon to generate the llbc output.
    let tmp_dir = tempfile::TempDir::new()?;
    let tmp_file_path = tmp_dir.path().join("example.llbc");
    let status = Command::cargo_bin("charon")?
        .arg("--no-cargo")
        .arg("--input")
        .arg(&input_file)
        .arg("--dest-file")
        .arg(&tmp_file_path)
        .status()?;
    assert!(status.success(), "Calling `charon` failed");

    // Compare the generated file against the stored one.
    let generated_crate_data = read_crate_data(&tmp_file_path)?;
    let expected_crate_data = read_crate_data(&output_file)?;
    let force_update = std::env::var("FORCE_UPDATE_VERSION_TEST").is_ok();
    if generated_crate_data != expected_crate_data {
        if generated_crate_data.charon_version != expected_crate_data.charon_version || force_update
        {
            // The crate version was changed (or we forced the update); update the committed file output.
            std::fs::rename(tmp_file_path, output_file)?;
        } else {
            // Note that this can also happen if the input file changed. In that case the update
            // must be done manually.
            anyhow::bail!("The llbc file format appears to have changed, yet the crate version was not updated. \
                Please update the crate version in `Cargo.toml` \
                or call `FORCE_UPDATE_VERSION_TEST=1 cargo test --test version`.")
        }
    }
    Ok(())
}
