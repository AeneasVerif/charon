use itertools::Itertools;
use serde_state::WithState;
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

        struct MonoStruct {
            inner: GenericStruct<SimpleStruct>
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

        enum UninhabitedVariantWithFields {
            Bar,
            Baz { x: u32, y: !, z: u32 },
        }

        struct Uninhabited(!);

        enum DiscriminantInNicheOfField<'a,T> {
            None,
            Some((usize, &'a T))
        }

        union MaybeUninitInt {
            x: u32,
            y: (),
        }

        union PackIntsUnion {
            x: (u32, u32),
            y: u64,
        }

        #[repr(C)]
        union PackIntsUnionC {
            x: (u32, u32),
            y: u64,
        }

        enum NonZeroNiche {
            A(char),
            B,
            C,
        }

        #[repr(C)]
        enum ReprC {
            A(char),
            B,
            C,
        }

        #[repr(C)]
        enum ReprCSingle {
            A(char),
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

        #[repr(C, i8)]
        enum E {
            A = 0,
            B(usize) = 12
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

        type Str = str;

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
                    if let Some(variant) = variant {
                        assert!(
                            variant.tagger.is_empty(),
                            "For type {name} with uninhabited variant {var_id} expected empty tagger",
                        );
                    }
                } else {
                    let Some(variant) = variant else {
                        panic!("For type {name} with inhabited variant {var_id} expected a layout");
                    };
                    let tagger = &variant.tagger;
                    // Use the tagger entries to answer discriminator read queries. For bytes
                    // not covered by the tagger (e.g. the untagged variant in niche encoding),
                    // we need a value that doesn't match any tagged variant's range.
                    let all_taggers = layout
                        .variant_layouts
                        .iter()
                        .filter_map(|v| v.as_ref())
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

    let layouts: SeqHashMap<String, _> = crate_data
        .type_decls
        .iter()
        .filter_map(|tdecl| {
            if tdecl.item_meta.name.name[0].as_ident().unwrap().0 != "test_crate" {
                return None;
            }
            let name = repr_name(&crate_data, &tdecl.item_meta.name);
            let opt_layout = tdecl.layout.get(&the_target).cloned();
            let serializable = opt_layout.map(|l| WithState::new(l, &()));
            Some((name, serializable))
        })
        .collect();
    let layouts_str = serde_json::to_string_pretty(&layouts)?;

    compare_or_overwrite(layouts_str, &PathBuf::from("./tests/layout.json"))?;

    let mut layout_computer = LayoutComputer::new(&crate_data, Some(&the_target));
    let layouts: SeqHashMap<String, _> = crate_data
        .type_decls
        .iter()
        .filter_map(|tdecl| {
            if tdecl.item_meta.name.name[0].as_ident().unwrap().0 != "test_crate" {
                return None;
            }
            let name = repr_name(&crate_data, &tdecl.item_meta.name);
            let opt_guarantee = tdecl.guarantees.clone();
            let fake_ty = Ty::new(TyKind::Adt(TypeDeclRef {
                id: TypeId::Adt(tdecl.def_id),
                generics: Box::new(tdecl.generics.identity_args()),
            }));
            let opt_concretized = layout_computer.compute_layout(fake_ty);

            // Check whether concretized layout guarantees always match known layouts.
            if let Some(layout) = tdecl.layout.get(&the_target)
                && let Some(guarantees) = &opt_concretized
                && let Some(size) = layout.size.concrete
                && let Some(align) = layout.align.concrete
                && let Some((size_guarantee, align_guarantee)) = guarantees.is_concrete()
            {
                assert_eq!(size, size_guarantee);
                assert_eq!(align, align_guarantee);
            }

            let guarantee_serializable = opt_guarantee.map(|l| WithState::new(l, &()));
            let concretized_serializable = opt_concretized.map(|l| WithState::new(l, &()));
            Some((name, (guarantee_serializable, concretized_serializable)))
        })
        .collect();
    let layouts_str = serde_json::to_string_pretty(&layouts)?;

    compare_or_overwrite(
        layouts_str,
        &PathBuf::from("./tests/layout_guarantees.json"),
    )?;
    Ok(())
}
