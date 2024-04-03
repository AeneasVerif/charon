#![feature(rustc_private)]

use std::{error::Error, fs::File};

use charon_lib::{export::GCrateData, llbc_ast};

extern crate log;
extern crate rustc_driver;

fn translate(
    code: impl std::fmt::Display,
) -> Result<GCrateData<llbc_ast::FunDecl, llbc_ast::GlobalDecl>, Box<dyn Error>> {
    use charon_lib::driver::CharonCallbacks;
    use charon_lib::*;
    use rustc_driver::RunCompiler;

    // Initialize the logger
    logger::initialize_logger();

    let mut compiler_args: Vec<String> = Vec::new();

    // Arguments list always start with the executable name. We put a silly value to ensure it's
    // not used for anything.
    compiler_args.push("__MYSTERIOUS_FIRST_ARG__".to_string());

    // Write the code to a temporary file.
    use std::io::Write;
    let tmp_dir = tempfile::TempDir::new()?;
    let file_path = tmp_dir.path().join("test_crate.rs");
    {
        let mut tmp_file = File::create(&file_path)?;
        write!(tmp_file, "{}", code)?;
        drop(tmp_file);
    }
    compiler_args.push(file_path.to_string_lossy().into_owned());

    // Call the Rust compiler with our custom callback.
    let mut callback = CharonCallbacks::new(Default::default());
    let res = RunCompiler::new(&compiler_args, &mut callback).run();
    // Extract the computed crate data.
    assert_eq!(callback.error_count, 0);
    assert!(res.is_ok());
    let export::CrateData::LLBC(crate_data) = callback.crate_data.unwrap() else {
        panic!("expected llbc data, got ullbc instead")
    };

    Ok(crate_data)
}

#[test]
fn type_decl() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        "
        struct Struct;
        fn main() {}
        ",
    )?;
    assert_eq!(
        serde_json::to_string(&crate_data.types[0].name.name).unwrap(),
        r#"[{"Ident":["test_crate",0]},{"Ident":["Struct",0]}]"#,
    );
    Ok(())
}
