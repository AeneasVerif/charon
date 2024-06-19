#![feature(rustc_private)]
#![feature(lint_reasons)]

use assert_cmd::prelude::{CommandCargoExt, OutputAssertExt};
use itertools::Itertools;
use std::collections::HashMap;
use std::{error::Error, fs::File, io::BufReader, process::Command};

use charon_lib::{
    export::CrateData, gast::*, logger, meta::*, names::*, types::*, values::ScalarValue,
};

fn translate(code: impl std::fmt::Display) -> Result<CrateData, Box<dyn Error>> {
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
    let crate_data: CrateData = {
        let file = File::open(output_path)?;
        let reader = BufReader::new(file);
        serde_json::from_reader(reader)?
    };

    Ok(crate_data)
}

/// `Name` is a complex datastructure; to inspect it we serialize it a little bit.
fn repr_name(crate_data: &CrateData, n: &Name) -> String {
    n.name
        .iter()
        .map(|path_elem| match path_elem {
            PathElem::Ident(i, _) => i.clone(),
            PathElem::Impl(elem) => match &elem.kind {
                ImplElemKind::Trait(trait_ref) => {
                    let trait_name = trait_name(crate_data, trait_ref.trait_id);
                    format!("<impl for {trait_name}>")
                }
                ImplElemKind::Ty(..) => "<impl>".to_string(),
            },
        })
        .join("::")
}

fn repr_span(span: Span) -> String {
    let raw_span = span.span;
    format!("{}-{}", raw_span.beg, raw_span.end)
}

fn trait_name(crate_data: &CrateData, trait_id: TraitDeclId) -> &str {
    let tr = &crate_data.trait_decls[trait_id.index()];
    let PathElem::Ident(trait_name, _) = tr.name.name.last().unwrap() else {
        panic!()
    };
    trait_name
}

enum ItemKind<'c> {
    Fun(&'c FunDecl),
    Global(&'c GlobalDecl),
    Type(&'c TypeDecl),
    TraitDecl(&'c TraitDecl),
    TraitImpl(&'c TraitImpl),
}

/// A general item, with information shared by all items.
#[expect(dead_code)]
struct Item<'c> {
    name: &'c Name,
    name_str: String,
    item_meta: &'c ItemMeta,
    // Not a ref because we do a little hack.
    generics: GenericParams,
    preds: &'c Predicates,
    kind: ItemKind<'c>,
}

/// Get all the items for this crate.
fn items_by_name<'c>(crate_data: &'c CrateData) -> HashMap<String, Item<'c>> {
    crate_data
        .functions
        .iter()
        .map(|x| Item {
            name: &x.name,
            name_str: repr_name(crate_data, &x.name),
            item_meta: &x.item_meta,
            generics: x.signature.generics.clone(),
            preds: &x.signature.preds,
            kind: ItemKind::Fun(x),
        })
        .chain(crate_data.globals.iter().map(|x| Item {
            name: &x.name,
            name_str: repr_name(crate_data, &x.name),
            item_meta: &x.item_meta,
            generics: x.generics.clone(),
            preds: &x.preds,
            kind: ItemKind::Global(x),
        }))
        .chain(crate_data.types.iter().map(|x| Item {
            name: &x.name,
            name_str: repr_name(crate_data, &x.name),
            item_meta: &x.item_meta,
            generics: x.generics.clone(),
            preds: &x.preds,
            kind: ItemKind::Type(x),
        }))
        .chain(crate_data.trait_impls.iter().map(|x| Item {
            name: &x.name,
            name_str: repr_name(crate_data, &x.name),
            item_meta: &x.item_meta,
            generics: x.generics.clone(),
            preds: &x.preds,
            kind: ItemKind::TraitImpl(x),
        }))
        .chain(crate_data.trait_decls.iter().map(|x| {
            let mut generics = x.generics.clone();
            // We do a little hack.
            assert!(generics.trait_clauses.is_empty());
            generics.trait_clauses = x.parent_clauses.clone();
            Item {
                name: &x.name,
                name_str: repr_name(crate_data, &x.name),
                item_meta: &x.item_meta,
                generics,
                preds: &x.preds,
                kind: ItemKind::TraitDecl(x),
            }
        }))
        .map(|item| (item.name_str.clone(), item))
        .collect()
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
        repr_name(&crate_data, &crate_data.types[0].name),
        "test_crate::Struct"
    );
    Ok(())
}

#[test]
fn file_name() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        "
        type Foo = Option<()>;
        ",
    )?;
    assert_eq!(
        repr_name(&crate_data, &crate_data.types[0].name),
        "test_crate::Foo"
    );
    assert_eq!(
        repr_name(&crate_data, &crate_data.types[1].name),
        "core::option::Option"
    );
    let file_id = crate_data.types[1].item_meta.span.span.file_id;
    let (_, file) = crate_data
        .id_to_file
        .iter()
        .find(|(i, _)| *i == file_id)
        .unwrap();
    let FileName::Virtual(file) = file else {
        panic!()
    };
    assert_eq!(file, "/rustc/library/core/src/option.rs");
    Ok(())
}

#[test]
fn spans() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        "
        pub fn sum(s: &[u32]) -> u32 {
            let mut sum = 0;
            let mut i = 0;
            while i < s.len() {
                sum += s[i];
                i += 1;
            }
            sum
        }
        ",
    )?;
    let function = &crate_data.functions[0];
    // Span of the function signature.
    assert_eq!(repr_span(function.item_meta.span), "2:8-2:36");
    let body_id = function.body.unwrap();
    let body = &crate_data.bodies[body_id].as_structured().unwrap().body;
    // The whole function declaration.
    assert_eq!(repr_span(body.span), "2:8-10:9");
    let seq = body.clone().into_sequence();
    let the_loop = seq.iter().find(|st| st.content.is_loop()).unwrap();
    // That's not a very precise span :/
    assert_eq!(repr_span(the_loop.span), "4:12-10:9");
    Ok(())
}

#[test]
fn predicate_origins() -> Result<(), Box<dyn Error>> {
    use PredicateOrigin::*;
    let crate_data = translate(
        "
        fn top_level_function<T: Clone>() where T: Default {}

        #[derive(Clone)]
        struct Struct<T: Clone> where T: Default { x: T }

        type TypeAlias<T: Clone> where T: Default = Struct<T>;

        impl<T: Clone> Struct<T> where T: Default {
            fn inherent_method<U: From<T>>() where T: From<U> {}
        }

        trait Trait<T: Copy>: Clone where T: Default {
            type AssocType: Default;
            fn trait_method<U: From<T>>() where T: From<U>;
        }

        impl<T: Copy> Trait<T> for Struct<T> where T: Default {
            type AssocType = ();
            fn trait_method<U: From<T>>() where T: From<U> {}
        }
        ",
    )?;
    let expected_function_clause_origins: Vec<(&str, &[_])> = vec![
        (
            "test_crate::top_level_function",
            &[(WhereClauseOnFn, "Clone"), (WhereClauseOnFn, "Default")],
        ),
        (
            "test_crate::Struct",
            &[(WhereClauseOnType, "Clone"), (WhereClauseOnType, "Default")],
        ),
        (
            "test_crate::TypeAlias",
            &[(WhereClauseOnType, "Clone"), (WhereClauseOnType, "Default")],
        ),
        (
            "test_crate::<impl>::inherent_method",
            &[
                (WhereClauseOnImpl, "Clone"),
                (WhereClauseOnImpl, "Default"),
                (WhereClauseOnFn, "From"),
                (WhereClauseOnFn, "From"),
            ],
        ),
        (
            "test_crate::Trait",
            &[
                (WhereClauseOnTrait, "Clone"),
                (WhereClauseOnTrait, "Copy"),
                (WhereClauseOnTrait, "Default"),
            ],
        ),
        // Interesting note: the method definition does not mention the clauses on the trait.
        (
            "test_crate::Trait::trait_method",
            &[(WhereClauseOnFn, "From"), (WhereClauseOnFn, "From")],
        ),
        (
            "test_crate::<impl for Trait>",
            &[(WhereClauseOnImpl, "Copy"), (WhereClauseOnImpl, "Default")],
        ),
        (
            "test_crate::<impl for Trait>::trait_method",
            &[
                (WhereClauseOnImpl, "Copy"),
                (WhereClauseOnImpl, "Default"),
                (WhereClauseOnFn, "From"),
                (WhereClauseOnFn, "From"),
            ],
        ),
    ];
    let items_by_name = items_by_name(&crate_data);
    for (item_name, origins) in expected_function_clause_origins {
        let Some(item) = items_by_name.get(item_name) else {
            let keys = items_by_name
                .keys()
                .sorted()
                .map(|k| format!("- `{k}`"))
                .join("\n");
            panic!("Item `{item_name}` not found. Available items: \n{keys}")
        };
        let clauses = &item.generics.trait_clauses;
        assert_eq!(origins.len(), clauses.len(), "failed for {item_name}");
        for (clause, (expected_origin, expected_trait_name)) in clauses.iter().zip(origins) {
            let trait_name = trait_name(&crate_data, clause.trait_id);
            assert_eq!(trait_name, *expected_trait_name, "failed for {item_name}");
            assert_eq!(&clause.origin, expected_origin, "failed for {item_name}");
        }
    }
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
    assert_eq!(
        repr_name(&crate_data, &crate_data.types[0].name),
        "test_crate::Pub"
    );
    assert!(crate_data.types[0].item_meta.public);
    assert_eq!(
        repr_name(&crate_data, &crate_data.types[1].name),
        "test_crate::Priv"
    );
    assert!(!crate_data.types[1].item_meta.public);
    // Note how we think `PubInPriv` is public. It kind of is but there is no path to it. This is
    // probably fine.
    assert_eq!(
        repr_name(&crate_data, &crate_data.types[2].name),
        "test_crate::private::PubInPriv"
    );
    assert!(crate_data.types[2].item_meta.public);
    Ok(())
}

#[test]
fn discriminants() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        r#"
        enum Foo {
            Variant1,
            Variant2,
        }
        #[repr(u32)]
        enum Bar {
            Variant1 = 3,
            Variant2 = 42,
        }
        "#,
    )?;
    fn get_enum_discriminants(ty: &TypeDecl) -> Vec<ScalarValue> {
        ty.kind.as_enum().iter().map(|v| v.discriminant).collect()
    }
    assert_eq!(
        get_enum_discriminants(&crate_data.types[0]),
        vec![ScalarValue::Isize(0), ScalarValue::Isize(1)]
    );
    assert_eq!(
        get_enum_discriminants(&crate_data.types[1]),
        vec![ScalarValue::U32(3), ScalarValue::U32(42)]
    );
    Ok(())
}

#[test]
fn rename_attribute() -> Result<(), Box<dyn Error>> {
    let crate_data = translate(
        r#"
        #![feature(register_tool)]
        #![register_tool(charon)]
        #![register_tool(aeneas)]
        
        #[charon::rename("BoolTest")]
        pub trait BoolTrait {
            // Required method
            #[charon::rename("getTest")]
            fn get_bool(&self) -> bool;

            // Provided method
            #[charon::rename("retTest")]
            fn ret_true(&self) -> bool {
                true
            }
        }

        #[charon::rename("BoolImpl")]
        impl BoolTrait for bool {
            fn get_bool(&self) -> bool {
                *self
            }
        }

        #[charon::rename("BoolFn")]
        fn test_bool_trait<T>(x: bool) -> bool {
            x.get_bool() && x.ret_true()
        }

        #[charon::rename("TypeTest")]
        type Test = i32;

        #[charon::rename("VariantsTest")]
        enum SimpleEnum {
            #[charon::rename("Variant1")]
            FirstVariant,
            SecondVariant,
            ThirdVariant,
        }

        #[charon::rename("StructTest")]
        struct Foo {
            #[charon::rename("FieldTest")]
            field1: u32,
        }

        #[charon::rename("Const_Test")]
        const C: u32 = 100 + 10 + 1;

        #[aeneas::rename("_TypeAeneas36")]
        type Test2 = u32;
        "#,
    )?;

    assert_eq!(
        crate_data.trait_decls[0].item_meta.rename.as_deref(),
        Some("BoolTest")
    );

    assert_eq!(
        crate_data.functions[2].item_meta.rename.as_deref(),
        Some("getTest")
    );

    assert_eq!(
        crate_data.functions[3].item_meta.rename.as_deref(),
        Some("retTest")
    );

    assert_eq!(
        crate_data.trait_impls[0].item_meta.rename.as_deref(),
        Some("BoolImpl")
    );

    assert_eq!(
        crate_data.functions[1].item_meta.rename.as_deref(),
        Some("BoolFn")
    );

    assert_eq!(
        crate_data.types[0].item_meta.rename.as_deref(),
        Some("TypeTest")
    );

    assert_eq!(
        crate_data.types[1].item_meta.rename.as_deref(),
        Some("VariantsTest")
    );

    assert_eq!(
        crate_data.types[1].kind.as_enum()[0]
            .item_meta
            .rename
            .as_deref(),
        Some("Variant1")
    );

    assert_eq!(
        crate_data.types[2].item_meta.rename.as_deref(),
        Some("StructTest")
    );

    assert_eq!(
        crate_data.globals[0].item_meta.rename.as_deref(),
        Some("Const_Test")
    );

    assert_eq!(
        crate_data.types[3].item_meta.rename.as_deref(),
        Some("_TypeAeneas36")
    );

    assert_eq!(
        crate_data.types[2].kind.as_struct()[0]
            .item_meta
            .rename
            .as_deref(),
        Some("FieldTest")
    );
    Ok(())
}
