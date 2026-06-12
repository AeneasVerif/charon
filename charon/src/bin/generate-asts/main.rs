use anyhow::{Context, Result, bail};
use assert_cmd::cargo::CommandCargoExt;
use charon_lib::ast::TranslatedCrate;
use charon_lib::options::SerializationFormat;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

mod generate_ml;
mod generate_rust;

fn run_charon(charon_llbc: &Path) -> Result<()> {
    let mut cmd = Command::cargo_bin("charon")?;
    cmd.arg("cargo");
    cmd.arg("--hide-marker-traits");
    cmd.arg("--hide-allocator");
    cmd.arg("--treat-box-as-builtin");
    cmd.arg("--ullbc");
    cmd.arg("--start-from=charon_lib::ast::krate::TranslatedCrate");
    cmd.arg("--start-from=charon_lib::ast::ullbc_ast::BodyContents");
    cmd.arg("--exclude=charon_lib::common::hash_by_addr::HashByAddr");
    cmd.arg(format!("--start-from={}", generate_rust::ATTRIBUTE_KIND));
    cmd.arg("--unbind-item-vars");
    cmd.arg("--sysroot=default");
    cmd.arg("--dest-file");
    cmd.arg(charon_llbc);
    cmd.arg("--");
    cmd.arg("--lib");
    cmd.arg("--features");
    cmd.arg("charon_on_charon");
    let output = cmd.output()?;

    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr.clone())?;
        bail!("Compilation failed: {stderr}")
    }
    Ok(())
}

fn translate_charon_itself(generated_dir: &Path) -> Result<TranslatedCrate> {
    let charon_llbc = generated_dir.join("charon-itself.ullbc");
    if std::env::var("CHARON_GENERATE_REUSE_LLBC").as_deref() != Ok("1") {
        run_charon(&charon_llbc)?;
    }

    charon_lib::deserialize_llbc_with_format(&charon_llbc, SerializationFormat::Json)
        .with_context(|| format!("Failed to deserialize {}", charon_llbc.display()))
}

fn main() -> Result<()> {
    let dir = PathBuf::from("src/bin/generate-asts");
    let generated_dir = dir.join("generated");
    fs::create_dir_all(&generated_dir)
        .with_context(|| format!("Failed to create {}", generated_dir.display()))?;

    let crate_data = translate_charon_itself(&generated_dir)?;

    let ml_output_dir = if std::env::var("IN_CI").as_deref() == Ok("1") {
        generated_dir
    } else {
        dir.join("../../../../charon-ml/src/generated")
    };
    generate_ml::generate(&crate_data, dir.join("templates"), ml_output_dir)?;
    generate_rust::generate(&crate_data)?;
    Ok(())
}
