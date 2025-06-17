#![feature(box_patterns)]
use std::path::PathBuf;

use indexmap::IndexMap;

use charon_lib::ast::*;

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
        "#,
    )?;

    // Check whether niche discriminant computations are correct, i.e. reversible.
    for tdecl in crate_data.type_decls.iter() {
        if let Some(layout) = tdecl.layout.as_ref() {
            if layout.discriminant_layout.is_some() {
                let name = repr_name(&crate_data, &tdecl.item_meta.name);
                let variants_from_kind = match &tdecl.kind {
                    TypeDeclKind::Enum(variants) => variants,
                    _ => unreachable!(),
                };
                for var_id in layout.variant_layouts.all_indices() {
                    let discr = variants_from_kind.get(var_id).unwrap().discriminant;

                    // As discussed in https://rust-lang.zulipchat.com/#narrow/channel/182449-t-compiler.2Fhelp/topic/.E2.9C.94.20VariantId.3DDiscriminant.20when.20tag.20is.20niche.20encoded.3F/with/524384295
                    // for niche-encoded tags, the variant id's should coincide with their discriminants.
                    if let Some(DiscriminantLayout {
                        encoding: TagEncoding::Niche { .. },
                        ..
                    }) = layout.discriminant_layout
                    {
                        assert_eq!(
                            var_id.raw() as u128,
                            discr.to_bits(),
                            "For type {} the discriminant {} is != the variant ID {}.",
                            name,
                            discr,
                            var_id
                        );
                    }

                    let tag = tdecl.get_tag_from_variant(var_id);
                    if tdecl.is_niche_discriminant(var_id) {
                        assert_eq!(None, tag, "For type {} something went wrong!", name);
                    } else if layout.is_variant_uninhabited(var_id) {
                        assert_eq!(
                            None, tag,
                            "For type {} with uninhabited variant {} something went wrong!",
                            name, var_id
                        );
                    } else {
                        let roundtrip_var_id =
                            tag.clone().and_then(|tag| tdecl.get_variant_from_tag(tag));
                        assert_eq!(
                            Some(var_id),
                            roundtrip_var_id,
                            "For type {} something went wrong, tag = {:?}",
                            name,
                            tag
                        );
                    }
                }
            }
        }
    }

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
    Ok(())
}
