#![feature(box_patterns)]
use itertools::Itertools;
use std::path::PathBuf;

use charon_lib::ast::*;

mod util;
use util::*;

#[test]
fn type_layout() -> anyhow::Result<()> {
    let crate_data = translate_rust_text(
        r#"
        #![feature(never_type)]
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

        // Unsupported for now
        // struct UnsizedStruct2 {
        //     x: usize,
        //     y: dyn std::fmt::Debug
        // }

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
            A(!),
            B(u32),
        }

        enum UninhabitedVariant2 {
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

        enum GenericButFixedSize<'a, T: Sized> {
            First,
            Second(&'a T),
        }

        #[repr(u128)]
        enum MaxBitsDiscr {
            First = 42,
            Second = 18446744073709551615,
        }

        type SingleVariantButNonZero = Result<!, ()>;

        type NonAdtAlias<T> = T;

        type Tuple = (u32, u32);

        type Usize = usize;

        type Ref<'a> = &'a mut u32;

        // See https://github.com/AeneasVerif/charon/issues/1046 : reading 3 is UB
        enum HasInvalidDiscr {
            Var1,       // variant 0, tag 2
            Var2(bool), // variant 1, untagged (valid values are 0=false and 1=true)
            Var3,       // variant 2, tag 4
        }
        "#,
        &[],
    )?;

    // Check whether discriminator/tagger roundtrips are correct: use each variant's tagger
    // to answer the discriminator's read queries, and verify we get back the same variant.
    let the_target = crate_data.target_information.keys().next().unwrap().clone();
    for tdecl in crate_data.type_decls.iter() {
        if let Some(layout) = tdecl.layout.get(&the_target)
            && let Some(discriminator) = &layout.discriminator
        {
            let name = repr_name(&crate_data, &tdecl.item_meta.name);
            for (var_id, variant) in layout.variant_layouts.iter_enumerated() {
                if layout.is_variant_uninhabited(var_id) {
                    assert!(
                        variant.tagger.is_empty(),
                        "For type {name} with uninhabited variant {var_id} expected empty tagger",
                    );
                } else {
                    let tagger = &variant.tagger;
                    // Use the tagger entries to answer discriminator read queries. For bytes
                    // not covered by the tagger (e.g. the untagged variant in niche encoding),
                    // we need a value that doesn't match any tagged variant's range.
                    let all_taggers = layout
                        .variant_layouts
                        .iter()
                        .flat_map(|v| v.tagger.iter())
                        .collect_vec();
                    let result = discriminator.read_discriminant(|offset, int_ty| {
                        Ok(tagger
                            .iter()
                            .find(|(off, val)| *off == offset && val.ty() == int_ty)
                            .map(|(_, val)| *val)
                            .unwrap_or_else(|| {
                                // Pick a value not used by any tagger at this offset.
                                let used_vals: Vec<_> = all_taggers
                                    .iter()
                                    .filter(|(off, _)| *off == offset)
                                    .map(|(_, val)| val.to_bits())
                                    .collect();
                                // Find a value not in the used set (try incrementing from the
                                // first used value).
                                let candidate = used_vals.iter().copied().max().unwrap_or(0) + 1;
                                ScalarValue::from_bits(int_ty, candidate)
                            }))
                    });
                    assert_eq!(
                        Ok(var_id),
                        result,
                        "For type {name} variant {var_id}, tagger = {tagger:?}",
                    );
                }
            }
        }
    }

    let layouts: SeqHashMap<String, Option<Layout>> = crate_data
        .type_decls
        .iter()
        .filter_map(|tdecl| {
            if tdecl.item_meta.name.name[0].as_ident().unwrap().0 != "test_crate" {
                return None;
            }
            let name = repr_name(&crate_data, &tdecl.item_meta.name);
            Some((name, tdecl.layout.get(&the_target).cloned()))
        })
        .collect();
    let layouts_str = serde_json::to_string_pretty(&layouts)?;

    compare_or_overwrite(layouts_str, &PathBuf::from("./tests/layout.json"))?;
    Ok(())
}
