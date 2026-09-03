use anyhow::{Context, Result, bail};
use assert_cmd::cargo::CommandCargoExt;
use charon_lib::ast::TranslatedCrate;
use charon_lib::options::SerializationFormat;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

mod generate_ml;
mod generate_rust;

fn run_charon(charon_llbc: &Path, rustc_datatypes: &generate_rust::RustcDatatypes) -> Result<()> {
    let mut cmd = Command::cargo_bin("charon")?;
    cmd.arg("cargo");
    cmd.arg("--hide-marker-traits");
    cmd.arg("--hide-allocator");
    cmd.arg("--treat-box-as-builtin");
    cmd.arg("--ullbc");
    cmd.arg("--start-from=charon_lib::ast::krate::TranslatedCrate");
    cmd.arg("--start-from=charon_lib::ast::bodies::unstructured::BodyContents");
    cmd.arg("--start-from=charon_lib::ast::meta::spans::SerializedSpan");
    cmd.arg("--exclude=charon_lib::utils::hash_by_addr::HashByAddr");
    for path in rustc_datatypes.paths_to_start_from() {
        cmd.arg(format!("--start-from={path}"));
    }
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

fn translate_charon_itself(
    generated_dir: &Path,
    rustc_datatypes: &generate_rust::RustcDatatypes,
) -> Result<TranslatedCrate> {
    let charon_llbc = generated_dir.join("charon-itself.ullbc");
    if std::env::var("CHARON_GENERATE_REUSE_LLBC").as_deref() != Ok("1") {
        run_charon(&charon_llbc, rustc_datatypes)?;
    }

    charon_lib::deserialize_llbc_with_format(&charon_llbc, SerializationFormat::Json)
        .with_context(|| format!("Failed to deserialize {}", charon_llbc.display()))
}

/// Substitute the declaration of `Span` (optimised for low memory) with that of `SerializedSpan`,
/// so OCaml doesn't deal with bit manipulations.
fn use_serialized_span(crate_data: &mut TranslatedCrate) -> Result<()> {
    let find = |name: &str| {
        crate_data
            .type_decls
            .iter()
            .find(|ty| ty.item_meta.name.debug_repr(crate_data) == name)
            .map(|ty| ty.def_id)
            .with_context(|| format!("Could not find type `{name}`"))
    };
    let serialized_span = find("charon_lib::ast::meta::spans::SerializedSpan")?;
    let span = find("charon_lib::ast::meta::spans::Span")?;
    crate_data.type_decls[span].kind = crate_data.type_decls[serialized_span].kind.clone();
    Ok(())
}

fn main() -> Result<()> {
    let dir = PathBuf::from("src/bin/generate-asts");
    let generated_dir = dir.join("generated");
    fs::create_dir_all(&generated_dir)
        .with_context(|| format!("Failed to create {}", generated_dir.display()))?;

    let rustc_datatypes = generate_rust::RustcDatatypes::new();
    let mut crate_data = translate_charon_itself(&generated_dir, &rustc_datatypes)?;
    use_serialized_span(&mut crate_data)?;

    let ml_output_dir = if std::env::var("IN_CI").as_deref() == Ok("1") {
        generated_dir
    } else {
        dir.join("../../../../charon-ml/src/generated")
    };
    generate_ml::generate(
        &crate_data,
        dir.join("generate_ml/templates"),
        ml_output_dir,
    )?;
    generate_rust::generate(&crate_data, &rustc_datatypes)?;
    Ok(())
}
