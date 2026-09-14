use anyhow::{Result, bail};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Run charon on this file with the given command line arguments. Returns the path to the
/// outputted `.llbc` file.
pub fn run_charon_on(file: &Path, charon_args: &[&str]) -> Result<PathBuf> {
    assert!(file.is_absolute());
    let example_name = file.parent().and_then(Path::file_name).unwrap();

    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output_dir = manifest_dir.join("target/charon-examples");
    std::fs::create_dir_all(&output_dir)?;
    let output_file = output_dir.join(example_name).with_extension("llbc");

    let output = Command::new(env!("CARGO"))
        .current_dir(manifest_dir)
        .args(["run", "--quiet", "--bin", "charon", "--", "rustc"])
        .arg("--format=json")
        .arg("--dest-file")
        .arg(&output_file)
        .args(charon_args)
        .arg("--")
        .arg(file)
        .args(["--crate-type=rlib", "--edition=2021"])
        .output()
        .unwrap();

    if output.status.success() {
        Ok(output_file)
    } else {
        bail!(
            "Charon failed on {}:\n{}",
            file.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
