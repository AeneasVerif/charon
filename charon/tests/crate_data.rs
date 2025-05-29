#![feature(box_patterns)]

use charon_lib::ast::{AnyTransItem, TranslatedCrate};
use itertools::Itertools;
use std::collections::HashMap;
use std::error::Error;

use charon_lib::llbc_ast::*;

mod util;

fn translate(code: impl std::fmt::Display) -> anyhow::Result<TranslatedCrate> {
    util::translate_rust_text(code)
}

/// `Name` is a complex datastructure; to inspect it we serialize it a little bit.
fn repr_name(crate_data: &TranslatedCrate, n: &Name) -> String {
    n.name
        .iter()
        .map(|path_elem| match path_elem {
            PathElem::Ident(i, _) => i.clone(),
            PathElem::Impl(elem, _) => match elem {
                ImplElem::Trait(impl_id) => match crate_data.trait_impls.get(*impl_id) {
                    None => format!("<trait impl#{impl_id}>"),
                    Some(timpl) => {
                        let trait_name = trait_name(crate_data, timpl.impl_trait.trait_id);
                        format!("<impl {trait_name} for ??>")
                    }
                },
                ImplElem::Ty(..) => "<inherent impl>".to_string(),
            },
            PathElem::Monomorphized(..) => "<mono>".to_string(),
        })
        .join("::")
}

fn repr_span(span: Span) -> String {
    let raw_span = span.span;
    format!("{}-{}", raw_span.beg, raw_span.end)
}

fn trait_name(crate_data: &TranslatedCrate, trait_id: TraitDeclId) -> &str {
    let tr = &crate_data.trait_decls[trait_id];
    let PathElem::Ident(trait_name, _) = tr.item_meta.name.name.last().unwrap() else {
        panic!()
    };
    trait_name
}

/// A general item, with information shared by all items.
struct Item<'c> {
    name_str: String,
    // Not a ref because we do a little hack.
    generics: GenericParams,
    #[expect(dead_code)]
    kind: AnyTransItem<'c>,
}

/// Get all the items for this crate.
fn items_by_name<'c>(crate_data: &'c TranslatedCrate) -> HashMap<String, Item<'c>> {
    crate_data
        .all_items()
        .map(|item| {
            let mut generics = item.generic_params().clone();
            if let AnyTransItem::TraitDecl(tdecl) = &item {
                // We do a little hack.
                assert!(generics.trait_clauses.is_empty());
                generics.trait_clauses = tdecl.parent_clauses.clone();
            }
            Item {
                name_str: repr_name(crate_data, &item.item_meta().name),
                generics,
                kind: item,
            }
        })
        .map(|item| (item.name_str.clone(), item))
        .collect()
}

#[test]
fn type_decl() -> anyhow::Result<()> {
    let crate_data = translate(
        "
        struct Struct;
        fn main() {}
        ",
    )?;
    assert_eq!(
        repr_name(&crate_data, &crate_data.type_decls[0].item_meta.name),
        "test_crate::Struct"
    );
    Ok(())
}

#[test]
fn file_name() -> anyhow::Result<()> {
    let crate_data = translate(
        "
        type Foo = Option<()>;
        ",
    )?;
    assert_eq!(
        repr_name(&crate_data, &crate_data.type_decls[0].item_meta.name),
        "test_crate::Foo"
    );
    assert_eq!(
        repr_name(&crate_data, &crate_data.type_decls[1].item_meta.name),
        "core::option::Option"
    );
    let file_id = crate_data.type_decls[1].item_meta.span.span.file_id;
    let file = &crate_data.files[file_id];
    assert_eq!(file.name.to_string(), "/rustc/library/core/src/option.rs");
    Ok(())
}

#[test]
fn spans() -> anyhow::Result<()> {
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
    let function = &crate_data.fun_decls[0];
    // Span of the whole function.
    assert_eq!(repr_span(function.item_meta.span), "2:8-10:9");

    let body = function.body.as_ref().unwrap();
    let body = &body.as_structured().unwrap().body;
    // Span of the function body
    assert_eq!(repr_span(body.span), "3:16-10:9");

    let the_loop = body
        .statements
        .iter()
        .find(|st| st.content.is_loop())
        .unwrap();
    assert_eq!(repr_span(the_loop.span), "5:12-8:13");

    Ok(())
}

#[test]
fn predicate_origins() -> anyhow::Result<()> {
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
    let expected_function_clause_origins: Vec<(&str, Vec<_>)> = vec![
        (
            "test_crate::top_level_function",
            vec![
                (WhereClauseOnFn, "Sized"),
                (WhereClauseOnFn, "Clone"),
                (WhereClauseOnFn, "Default"),
            ],
        ),
        (
            "test_crate::Struct",
            vec![
                (WhereClauseOnType, "Sized"),
                (WhereClauseOnType, "Clone"),
                (WhereClauseOnType, "Default"),
            ],
        ),
        (
            "test_crate::TypeAlias",
            vec![
                (WhereClauseOnType, "Sized"),
                (WhereClauseOnType, "Clone"),
                (WhereClauseOnType, "Default"),
            ],
        ),
        (
            "test_crate::<inherent impl>::inherent_method",
            vec![
                (WhereClauseOnImpl, "Sized"),
                (WhereClauseOnImpl, "Clone"),
                (WhereClauseOnImpl, "Default"),
                (WhereClauseOnFn, "Sized"),
                (WhereClauseOnFn, "From"),
                (WhereClauseOnFn, "From"),
            ],
        ),
        (
            "test_crate::Trait",
            vec![
                (WhereClauseOnTrait, "Clone"),
                (WhereClauseOnTrait, "Sized"),
                (WhereClauseOnTrait, "Copy"),
                (WhereClauseOnTrait, "Default"),
                (TraitItem(TraitItemName("AssocType".to_owned())), "Sized"),
                (TraitItem(TraitItemName("AssocType".to_owned())), "Default"),
            ],
        ),
        // Interesting note: the method definition does not mention the clauses on the trait.
        (
            "test_crate::Trait::trait_method",
            vec![
                (WhereClauseOnFn, "Sized"),
                (WhereClauseOnFn, "From"),
                (WhereClauseOnFn, "From"),
            ],
        ),
        (
            "test_crate::<impl Trait for ??>",
            vec![
                (WhereClauseOnImpl, "Sized"),
                (WhereClauseOnImpl, "Copy"),
                (WhereClauseOnImpl, "Default"),
            ],
        ),
        (
            "test_crate::<impl Trait for ??>::trait_method",
            vec![
                (WhereClauseOnImpl, "Sized"),
                (WhereClauseOnImpl, "Copy"),
                (WhereClauseOnImpl, "Default"),
                (WhereClauseOnFn, "Sized"),
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
        assert_eq!(
            origins.len(),
            clauses.elem_count(),
            "failed for {item_name}"
        );
        for (clause, (expected_origin, expected_trait_name)) in clauses.iter().zip(origins) {
            let trait_name = trait_name(&crate_data, clause.trait_.skip_binder.trait_id);
            assert_eq!(trait_name, expected_trait_name, "failed for {item_name}");
            assert_eq!(&clause.origin, &expected_origin, "failed for {item_name}");
        }
    }

    Ok(())
}

#[test]
fn attributes() -> anyhow::Result<()> {
    // Use the `clippy::` prefix because it's ignored by rustc.
    let unknown_attrs = |item_meta: &ItemMeta| {
        item_meta
            .attr_info
            .attributes
            .iter()
            .filter_map(|a| a.as_unknown())
            .map(|a| a.to_string())
            .collect_vec()
    };
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
        /// This is a doc comment.
        fn main() {}
        "#,
    )?;
    assert_eq!(
        unknown_attrs(&crate_data.type_decls[0].item_meta),
        vec!["clippy::foo", "clippy::foo(arg)", "clippy::foo(\"arg\")"]
    );
    assert_eq!(
        unknown_attrs(&crate_data.type_decls[1].item_meta),
        vec!["non_exhaustive"]
    );
    assert_eq!(
        unknown_attrs(&crate_data.trait_decls[0].item_meta),
        vec!["clippy::foo"]
    );
    assert_eq!(
        unknown_attrs(&crate_data.trait_impls[0].item_meta),
        vec!["clippy::foo"]
    );
    assert_eq!(
        unknown_attrs(&crate_data.global_decls[0].item_meta),
        vec!["clippy::foo"]
    );
    assert_eq!(
        unknown_attrs(&crate_data.global_decls[1].item_meta),
        vec!["clippy::foo"]
    );
    // We don't parse that attribute ourselves, we let rustc do it.
    assert_eq!(
        unknown_attrs(&crate_data.fun_decls[0].item_meta),
        vec!["inline(never)"]
    );
    assert_eq!(
        crate_data.fun_decls[0].item_meta.attr_info.inline,
        Some(InlineAttr::Never)
    );
    assert_eq!(
        crate_data.fun_decls[0]
            .item_meta
            .attr_info
            .attributes
            .last()
            .unwrap(),
        &Attribute::DocComment(" This is a doc comment.".to_owned())
    );
    Ok(())
}

#[test]
fn visibility() -> anyhow::Result<()> {
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
        repr_name(&crate_data, &crate_data.type_decls[0].item_meta.name),
        "test_crate::Pub"
    );
    assert!(crate_data.type_decls[0].item_meta.attr_info.public);
    assert_eq!(
        repr_name(&crate_data, &crate_data.type_decls[1].item_meta.name),
        "test_crate::Priv"
    );
    assert!(!crate_data.type_decls[1].item_meta.attr_info.public);
    // Note how we think `PubInPriv` is public. It kind of is but there is no path to it. This is
    // probably fine.
    assert_eq!(
        repr_name(&crate_data, &crate_data.type_decls[2].item_meta.name),
        "test_crate::private::PubInPriv"
    );
    assert!(crate_data.type_decls[2].item_meta.attr_info.public);
    Ok(())
}

#[test]
fn discriminants() -> anyhow::Result<()> {
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
        ty.kind
            .as_enum()
            .unwrap()
            .iter()
            .map(|v| v.discriminant)
            .collect()
    }
    assert_eq!(
        get_enum_discriminants(&crate_data.type_decls[0]),
        vec![ScalarValue::Isize(0), ScalarValue::Isize(1)]
    );
    assert_eq!(
        get_enum_discriminants(&crate_data.type_decls[1]),
        vec![ScalarValue::U32(3), ScalarValue::U32(42)]
    );
    Ok(())
}

#[test]
fn rename_attribute() -> anyhow::Result<()> {
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
        #[charon::variants_prefix("Simple")]
        #[charon::variants_suffix("_")]
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
        crate_data.trait_decls[0]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("BoolTest")
    );

    assert_eq!(
        crate_data.fun_decls[0]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("BoolFn")
    );

    assert_eq!(
        crate_data.fun_decls[1]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("getTest")
    );

    assert_eq!(
        crate_data.fun_decls[2]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("retTest")
    );

    assert_eq!(
        crate_data.fun_decls[4]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("Const_Test")
    );

    assert_eq!(
        crate_data.trait_impls[0]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("BoolImpl")
    );

    assert_eq!(
        crate_data.type_decls[0]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("TypeTest")
    );

    assert_eq!(
        crate_data.type_decls[1]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("VariantsTest")
    );

    assert_eq!(
        crate_data.type_decls[1].kind.as_enum().unwrap()[0].renamed_name(),
        "Variant1"
    );
    assert_eq!(
        crate_data.type_decls[1].kind.as_enum().unwrap()[1].renamed_name(),
        "SimpleSecondVariant_"
    );

    assert_eq!(
        crate_data.type_decls[2]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("StructTest")
    );

    assert_eq!(
        crate_data.global_decls[0]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("Const_Test")
    );

    assert_eq!(
        crate_data.type_decls[3]
            .item_meta
            .attr_info
            .rename
            .as_deref(),
        Some("_TypeAeneas36")
    );

    assert_eq!(
        crate_data.type_decls[2].kind.as_struct().unwrap()[0]
            .attr_info
            .rename
            .as_deref(),
        Some("FieldTest")
    );
    Ok(())
}

#[test]
fn declaration_groups() -> anyhow::Result<()> {
    let crate_data = translate(
        r#"
        fn foo() {
            panic!()
        }
        trait Foo {
            const FOO: usize = 42;
        }
        impl Foo for () {}
        "#,
    )?;

    // There are two function ids registered, but only one is nonempty. `functions.len() == 2` as
    // `len()` counts the empty slots too.
    let decl_groups = crate_data.ordered_decls.unwrap();
    assert_eq!(crate_data.fun_decls.iter().count(), 2);
    assert_eq!(decl_groups.len(), 5);
    assert!(decl_groups
        .iter()
        .all(|group| group.to_mixed_group().is_non_rec()));

    Ok(())
}

#[test]
fn source_text() -> anyhow::Result<()> {
    let crate_data = translate(
        r#"
        fn foo() {
            panic!()
        }
        mod bar {
            fn baz( x : usize )  ->() { 
            let _ = x;
                } fn quux () {}
        }
        struct Foo { x: usize }
        trait Trait {
            fn method() {}
        }
        impl Trait for () {}
        "#,
    )?;

    let sources = crate_data
        .all_items()
        .map(|i| i.item_meta().source_text.as_ref().unwrap())
        .collect_vec();
    assert_eq!(sources[0], "fn foo() {\n            panic!()\n        }");
    assert_eq!(
        sources[1],
        "fn baz( x : usize )  ->() { \n            let _ = x;\n                }"
    );
    assert_eq!(sources[2], "fn quux () {}");
    assert_eq!(sources[3], "struct Foo { x: usize }");
    assert_eq!(
        sources[4],
        "trait Trait {\n            fn method() {}\n        }"
    );
    assert_eq!(sources[5], "impl Trait for () {}");
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
    let function = &crate_data.fun_decls[0];
    assert_eq!(
        repr_name(&crate_data, &function.item_meta.name),
        "test_crate::use_default"
    );
    let body = function.body.as_ref().unwrap();
    let body = &body.as_structured().unwrap().body;
    let [first_stmt, ..] = body.statements.as_slice() else {
        panic!()
    };
    let RawStatement::Call(call) = &first_stmt.content else {
        panic!()
    };
    let FnOperand::Regular(fn_ptr) = &call.func else {
        panic!()
    };
    // Assert that this call referes to the method directly, without using a trait ref.
    let FunIdOrTraitMethodRef::Fun(FunId::Regular(id)) = fn_ptr.func.as_ref() else {
        panic!()
    };
    // This is the function that gets called.
    let function = &crate_data.fun_decls[id.index()];
    assert_eq!(
        repr_name(&crate_data, &function.item_meta.name),
        "test_crate::<impl Default for ??>::default"
    );
    let ItemKind::TraitImpl { .. } = &function.kind else {
        panic!()
    };
    Ok(())
}

#[test]
fn type_layout() -> anyhow::Result<()> {
    let crate_data = translate(
        r#"
        use std::num::NonZero;

        struct SimpleStruct {
            x: u32,
            y: u32,
            z: u32
        }

        struct GenericStruct<T> {
            a: usize,
            b: T
        }

        struct UnsizedStruct {
            x: usize,
            y: [usize]
        }

        enum SimpleEnum {
            Var1,
            Other,
        }

        enum SimpleAdt {
            EmptyVar,
            StructVar { x: usize, y: usize },
            TupleVar(u32, u32),
        }

        enum NicheAdt {
            None,
            Some(NonZero<u32>)
        }

        struct IsAZST;
        "#,
    )?;

    let default_layout = Layout::default();
    let default_variant_layout = VariantLayout::default();

    // SimpleStruct
    assert_eq!(
        crate_data.type_decls[0].layout,
        Layout {
            size: Some(12),
            align: Some(4),
            discriminant_offset: None,
            variant_layouts: Vector::new()
        }
    );
    // GenericStruct
    assert_eq!(&crate_data.type_decls[1].layout, &default_layout);
    // UnsizedStruct
    assert_eq!(
        &crate_data.type_decls[2].layout,
        &Layout {
            align: Some(8),
            ..default_layout.clone()
        }
    );
    // SimpleEnum
    let mut variant_layouts = Vector::with_capacity(2);
    variant_layouts.push(default_variant_layout.clone());
    variant_layouts.push(default_variant_layout.clone());
    assert_eq!(
        &crate_data.type_decls[3].layout,
        &Layout {
            size: Some(1),
            align: Some(1),
            discriminant_offset: Some(0),
            variant_layouts
        }
    );
    // SimpleAdt
    let mut variant_layouts = Vector::with_capacity(2);
    variant_layouts.push(default_variant_layout.clone());
    let mut var2_offsets = Vector::with_capacity(2);
    var2_offsets.push(8);
    var2_offsets.push(16);
    variant_layouts.push(VariantLayout {
        field_offsets: var2_offsets,
    });
    let mut var3_offsets = Vector::with_capacity(2);
    var3_offsets.push(4);
    var3_offsets.push(8);
    variant_layouts.push(VariantLayout {
        field_offsets: var3_offsets,
    });
    assert_eq!(
        &crate_data.type_decls[4].layout,
        &Layout {
            size: Some(24),
            align: Some(8),
            discriminant_offset: Some(0),
            variant_layouts
        }
    );
    // NicheAdt
    assert_eq!(
        &crate_data.type_decls[5].layout,
        &Layout {
            size: Some(4),
            align: Some(4),
            ..default_layout.clone()
        }
    );
    // IsAZST
    assert_eq!(
        &crate_data.type_decls[6].layout,
        &Layout {
            size: Some(0),
            align: Some(1),
            ..default_layout
        }
    );
    Ok(())
}
