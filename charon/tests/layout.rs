use std::path::PathBuf;

use indexmap::IndexMap;

use charon_lib::{
    ast::{layout_computer::LayoutComputer, *},
    formatter::AstFormatter,
    pretty::{self, FmtWithCtx},
};

mod util;
use util::*;

#[test]
fn type_layout() -> anyhow::Result<()> {
    let crate_data = translate_rust_text(
        r#"
        #![feature(never_type)]
        use std::num::NonZero;
        use std::fmt::Debug;

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

        struct UnsizedStruct2 {
            x: usize,
            y: dyn Debug
        }

        struct GenericWithKnownLayout<T> {
            x: usize,
            y: Box<T>,
        }

        // Rust reorders the fields to save space.
        struct Reordered {
            x: u8,
            y: u32,
            z: u8,
        }

        // `repr(C)` prevents reordering the fields.
        #[repr(C)]
        struct NotReordered {
            x: u8,
            y: u32,
            z: u8,
        }

        #[repr(packed)]
        struct Packed {
            x: u8,
            y: u32,
            z: u8,
        }

        enum UninhabitedVariant {
            A(!, u32),
            B(u32),
        }

        struct Uninhabited(!);

        enum DiscriminantInNicheOfField<'a,T> {
            None,
            Some((usize, &'a T))
        }

        union PackIntsUnion {
            x: (u32, u32),
            y: u64,
        }

        enum NonZeroNiche {
            A(char),
            B,
            C,
        }

        #[repr(i32)]
        enum ArbitraryDiscriminants {
            A(String) = 12,
            B(u32) = 43,
            C = 123456,
        }

        #[repr(i8)]
        enum MyOrder {
            Less = -1,
            Equal = 0,
            Greater = 1,
        }

        enum WithNicheAndUninhabited {
            First,
            Second(!),
            Third(NonZero<u32>)
        }

        enum GenericUnsized<'a, T: ?Sized> {
            First,
            Second(&'a T),
        }

        #[derive(Debug)]
        enum GenericButFixedSize<'a, T: Sized> {
            First,
            Second(&'a T),
        }

        #[repr(u128)]
        enum MaxBitsDiscr {
            First = 42,
            Second = 18446744073709551615,
        }

        struct NestedPointers<N> {
            x: (Box<N>, Box<N>),
            n: N
        }
        "#,
        &[],
    )?;

    // Check whether niche discriminant computations are correct, i.e. reversible.
    for tdecl in crate_data.type_decls.iter() {
        if let Some(layout) = tdecl.layout.as_ref() {
            if layout.discriminant_layout.is_some() {
                let name = repr_name(&crate_data, &tdecl.item_meta.name);
                for (var_id, variant) in layout.variant_layouts.iter_indexed() {
                    let tag = variant.tag;
                    if layout.is_variant_uninhabited(var_id) {
                        assert_eq!(
                            None, tag,
                            "For type {} with uninhabited variant {} something went wrong!",
                            name, var_id
                        );
                    } else {
                        match tag {
                            None => (), // Must be the untagged variant
                            Some(tag) => {
                                let roundtrip_var_id = tdecl.get_variant_from_tag(tag.clone());
                                assert_eq!(
                                    Some(var_id),
                                    roundtrip_var_id,
                                    "For type {} something went wrong, tag = {:?}",
                                    name,
                                    tag
                                )
                            }
                        }
                    }
                }
            }
        }
    }

    let mut layout_computer = LayoutComputer::new(&crate_data);
    let mut layouts_hints = IndexMap::new();
    let mut ctx = pretty::formatter::FmtCtx::new();
    ctx.translated = Some(&crate_data);
    {
        // Visit all types without context.
        let mut ty_visitor = DynVisitor::new_shared(|ty: &Ty| {
            let layout = layout_computer.get_layout_of(ty, None);
            let id = ty.to_string_with_ctx(&ctx);
            let _ = layouts_hints.insert(id, layout);
        });
        let _ = crate_data.drive(&mut ty_visitor);
    }
    {
        // Visit all type declarations with the corresponding context.
        let mut tdecl_visitor = DynVisitor::new_shared(|tdecl: &TypeDecl| {
            let generic_ctx = Some(&tdecl.generics);
            let ctx = ctx.set_generics(&tdecl.generics);
            if tdecl.kind.is_struct() {
                for arg in tdecl.kind.as_struct().unwrap() {
                    let layout = layout_computer.get_layout_of(&arg.ty, generic_ctx);
                    let id = arg.ty.to_string_with_ctx(&ctx);
                    let _ = layouts_hints.insert(id, layout);
                }
            }
        });
        let _ = crate_data.drive(&mut tdecl_visitor);
    }
    let layouts_hints_str = serde_json::to_string_pretty(&layouts_hints)?;

    let layouts: IndexMap<String, Option<Layout>> = crate_data
        .type_decls
        .iter()
        .filter_map(|tdecl| {
            if tdecl.item_meta.name.name[0].as_ident().unwrap().0 != "test_crate" {
                return None;
            }
            let name = repr_name(&crate_data, &tdecl.item_meta.name);
            Some((name, tdecl.layout.clone()))
        })
        .collect();
    let layouts_str = serde_json::to_string_pretty(&layouts)?;

    let action = if std::env::var("IN_CI").as_deref() == Ok("1") {
        Action::Verify
    } else {
        Action::Overwrite
    };
    compare_or_overwrite(action, layouts_str, &PathBuf::from("./tests/layout.json"))?;
    compare_or_overwrite(
        action,
        layouts_hints_str,
        &PathBuf::from("./tests/layouts_and_hints.json"),
    )?;
    Ok(())
}

#[test]
// Tests that the generic context of a declaration is correctly used to determine that pointers
// need no metadata for type variables that are (implicitly) `Sized`.
fn metadata() -> anyhow::Result<()> {
    let crate_data = translate_rust_text(
        r#"
        struct HasSizedParams<'a, T,S> {
            x: u32,
            y: Box<T>,
            z: &'a S
        }

        fn has_sized_params<'a,T: Sized,S>(_x: u32, y: Box<T>, _z: &'a S) -> &T {&*Box::leak(y)}
        "#,
        &[],
    )?;

    let mut layout_computer = LayoutComputer::new(&crate_data);
    {
        let mut tdecl_visitor = DynVisitor::new_shared(|tdecl: &TypeDecl| {
            let generic_ctx = Some(&tdecl.generics);
            if tdecl.kind.is_struct() {
                for arg in tdecl.kind.as_struct().unwrap() {
                    if arg.ty.is_box() {
                        let tvar = arg
                            .ty
                            .as_adt()
                            .unwrap()
                            .generics
                            .types
                            .get(TypeVarId::ZERO)
                            .unwrap();
                        assert!(tvar.is_type_var());
                        assert_eq!(tvar.needs_metadata(&crate_data, generic_ctx), Some(false));
                        let arg_layout = layout_computer.get_layout_of(&arg.ty, generic_ctx);
                        assert!(arg_layout.is_some_and(|e| e.is_left()));
                    } else if arg.ty.is_ref() {
                        let tvar = arg.ty.as_ref().unwrap().1;
                        assert!(tvar.is_type_var());
                        assert_eq!(tvar.needs_metadata(&crate_data, generic_ctx), Some(false));
                        let arg_layout = layout_computer.get_layout_of(&arg.ty, generic_ctx);
                        assert!(arg_layout.is_some_and(|e| e.is_left()));
                    }
                    assert_eq!(arg.ty.needs_metadata(&crate_data, generic_ctx), Some(false));
                }
            }
        });
        let _ = crate_data.drive(&mut tdecl_visitor);
    }

    let mut fun_sig_visitor = DynVisitor::new_shared(|fun_decl: &FunDecl| {
        if fun_decl.item_meta.name.name[0].as_ident().unwrap().0 == "test_crate" {
            let fun_sig = &fun_decl.signature;
            let generic_ctx = Some(&fun_sig.generics);
            for arg in &fun_sig.inputs {
                if arg.is_box() {
                    let tvar = arg
                        .as_adt()
                        .unwrap()
                        .generics
                        .types
                        .get(TypeVarId::ZERO)
                        .unwrap();
                    assert!(tvar.is_type_var());
                    assert_eq!(tvar.needs_metadata(&crate_data, generic_ctx), Some(false));
                    let arg_layout = layout_computer.get_layout_of(arg, generic_ctx);
                    assert!(arg_layout.is_some_and(|e| e.is_left()));
                } else if arg.is_ref() {
                    let tvar = arg.as_ref().unwrap().1;
                    assert!(tvar.is_type_var());
                    assert_eq!(tvar.needs_metadata(&crate_data, generic_ctx), Some(false));
                    let arg_layout = layout_computer.get_layout_of(arg, generic_ctx);
                    assert!(arg_layout.is_some_and(|e| e.is_left()));
                }
                assert_eq!(arg.needs_metadata(&crate_data, generic_ctx), Some(false));
            }
            let tvar = fun_sig.output.as_ref().unwrap().1;
            assert!(tvar.is_type_var());
            assert_eq!(tvar.needs_metadata(&crate_data, generic_ctx), Some(false));
            let ret_layout = layout_computer.get_layout_of(&fun_sig.output, generic_ctx);
            assert!(ret_layout.is_some_and(|e| e.is_left()));
        }
    });
    let _ = crate_data.drive(&mut fun_sig_visitor);

    Ok(())
}
