#![feature(rustc_private)]

use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
use itertools::Itertools;
use std::{error::Error, fs::File, io::BufReader, process::Command};

use charon_lib::{
    export::GCrateData,
    llbc_ast::{self, RawStatement},
    logger,
    meta::InlineAttr,
    names::{Name, PathElem},
    ullbc_ast::{FnOperand, FunIdOrTraitMethodRef},
};

fn translate(
    code: impl std::fmt::Display,
) -> Result<GCrateData<llbc_ast::FunDecl, llbc_ast::GlobalDecl>, Box<dyn Error>> {
    // Initialize the logger
    logger::initialize_logger();

    // Write the code to a temporary file.
    use std::io::Write;
    let tmp_dir = tempfile::TempDir::new()?;
    let input_path = tmp_dir.path().join("test_crate.rs");
    {
        let mut tmp_file = File::create(&input_path)?;
        write!(tmp_file, "{}", code)?;
        drop(tmp_file);
    }

    // Call charon
    let output_path = tmp_dir.path().join("test_crate.llbc");
    Command::cargo_bin("charon")?
        .arg("--no-cargo")
        .arg("--input")
        .arg(input_path)
        .arg("--dest-file")
        .arg(&output_path)
        .assert()
        .try_success()?;

    // Extract the computed crate data.
    let crate_data: GCrateData<_, _> = {
        let file = File::open(output_path)?;
        let reader = BufReader::new(file);
        serde_json::from_reader(reader)?
    };

    Ok(crate_data)
}

/// `Name` is a complex datastructure; to inspect it we serialize it a little bit.
fn repr_name(n: &Name) -> String {
    n.name
        .iter()
        .map(|path_elem| match path_elem {
            PathElem::Ident(i, _) => i,
            PathElem::Impl(_) => "<impl>",
        })
        .join("::")
}

#[test]
fn type_decl() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        "
        struct Struct;
        fn main() {}
        ",
    )?;
    assert_eq!(repr_name(&crate_data.types[0].name), "test_crate::Struct");
    Ok(())
}

#[test]
fn attributes() -> Result<(), Box<dyn Error>> {
    // Use the `clippy::` prefix because it's ignored by rustc.
    let crate_data = translate(
        r#"
        #[clippy::foo]
        #[clippy::foo(arg)]
        #[clippy::foo = "arg"]
        struct Struct;

        #[non_exhaustive]
        enum Enum {}

        #[clippy::foo]
        trait Trait {}

        #[clippy::foo]
        impl Trait for Struct {}

        #[clippy::foo]
        const FOO: () = ();

        #[clippy::foo]
        static BAR: () = ();

        #[inline(never)]
        fn main() {}
        "#,
    )?;
    assert_eq!(
        crate_data.types[0].item_meta.attributes,
        vec!["clippy::foo", "clippy::foo(arg)", "clippy::foo = \"arg\""]
    );
    assert_eq!(
        crate_data.types[1].item_meta.attributes,
        vec!["non_exhaustive"]
    );
    assert_eq!(
        crate_data.trait_decls[0].item_meta.attributes,
        vec!["clippy::foo"]
    );
    assert_eq!(
        crate_data.trait_impls[0].item_meta.attributes,
        vec!["clippy::foo"]
    );
    assert_eq!(
        crate_data.globals[0].item_meta.attributes,
        vec!["clippy::foo"]
    );
    assert_eq!(
        crate_data.globals[1].item_meta.attributes,
        vec!["clippy::foo"]
    );
    assert_eq!(
        crate_data.functions[0].item_meta.attributes,
        vec!["inline(never)"]
    );
    assert_eq!(
        crate_data.functions[0].item_meta.inline,
        Some(InlineAttr::Never)
    );
    Ok(())
}

#[test]
fn visibility() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        r#"
        pub struct Pub;
        struct Priv;

        mod private {
            pub struct PubInPriv;
        }
        "#,
    )?;
    assert_eq!(repr_name(&crate_data.types[0].name), "test_crate::Pub");
    assert!(crate_data.types[0].item_meta.public);
    assert_eq!(repr_name(&crate_data.types[1].name), "test_crate::Priv");
    assert!(!crate_data.types[1].item_meta.public);
    // Note how we think `PubInPriv` is public. It kind of is but there is no path to it. This is
    // probably fine.
    assert_eq!(
        repr_name(&crate_data.types[2].name),
        "test_crate::private::PubInPriv"
    );
    assert!(crate_data.types[2].item_meta.public);
    Ok(())
}

#[test]
fn known_trait_method_call() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        r#"
        #[derive(Default)]
        struct Struct;
        fn use_default() -> Struct {
            Struct::default()
        }
        "#,
    )?;
    let function = &crate_data.functions[1];
    assert_eq!(repr_name(&function.name), "test_crate::use_default");
    let body = &function.body.as_ref().unwrap().body;
    let RawStatement::Sequence(first_stmt, _) = &body.content else {
        panic!()
    };
    let RawStatement::Call(call) = &first_stmt.content else {
        panic!()
    };
    let FnOperand::Regular(fn_ptr) = &call.func else {
        panic!()
    };
    // Assert that this call referes to the method directly, without using a trait ref.
    let FunIdOrTraitMethodRef::Fun(..) = &fn_ptr.func else {
        panic!()
    };
    Ok(())
}
