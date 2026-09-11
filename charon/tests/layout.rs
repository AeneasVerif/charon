use itertools::Itertools;
use std::{borrow::Cow, fmt::Write, path::PathBuf};

use charon_lib::{
    ast::*,
    formatter::FmtCtx,
    pretty::{FmtWithCtx, fmt_with_ctx::TypeDeclFmtCtx},
    ullbc_ast::layout_guarantee_utils::{LayoutGuaranteeHelper, LayoutGuarantees},
};

mod util;
use util::*;

const CRATE_SOURCE: &'static str = r#"
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

        enum NicheAdtSigned {
            None,
            Some(NonZero<i32>),
        }

        enum NicheAdtChar {
            None,
            Some(char),
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

        type Str = str;

        type Ref<'a> = &'a mut u32;

        // See https://github.com/AeneasVerif/charon/issues/1046 : reading 3 is UB
        enum HasInvalidDiscr {
            Var1,       // variant 0, tag 2
            Var2(bool), // variant 1, untagged (valid values are 0=false and 1=true)
            Var3,       // variant 2, tag 4
        }

        // Signed tag: the niche is -2, and the valid range -2..=1 wraps around in bits
        // (0xFE..=0x01). Values outside -2..=1 are invalid.
        enum NicheInSignedRepr {
            A(MyOrder),
            B,
        }

        // Has a niche at offset 8
        #[repr(C)]
        struct BigWithChar {
            a: u64,
            c: char,
        }

        // The uninhabited variant `A` still gets a reserved niche value (0x110000), which must
        // not be attributed to the untagged variant `C`!
        enum UninhabitedAtNicheEdge {
            A(u32, !),
            B,
            C(BigWithChar),
        }

        // The untagged variant is uninhabited: reading any non-niche value is UB.
        enum UninhabitedUntagged {
            A(char, !),
            B,
        }
        "#;

#[test]
fn layout_discriminator_tagger() -> anyhow::Result<()> {
    let crate_data = translate_rust_text(CRATE_SOURCE, &[])?;
    let the_target = crate_data.target_information.keys().next().unwrap().clone();
    assert_eq!(
        crate_data.target_information[&the_target].c_enum_smallest_repr_ty,
        IntTy::I32,
    );

    // Check whether discriminator/tagger roundtrips are correct: use each variant's tagger
    // to answer the discriminator's read queries, and verify we get back the same variant.
    for tdecl in crate_data.type_decls.iter() {
        if let Some(layout) = tdecl.layout.get(&the_target)
            && let Some(discriminator) = &layout.discriminator
        {
            let name = tdecl.item_meta.name.debug_repr(&crate_data);
            for (var_id, variant) in layout.variant_layouts.iter_enumerated() {
                match layout.is_variant_uninhabited(var_id) {
                    Some(true) => {
                        if let Some(variant) = variant {
                            assert!(
                                variant.tagger.is_empty(),
                                "For type {name} with uninhabited variant {var_id} expected empty tagger",
                            );
                        }
                    }
                    Some(false) => {
                        let Some(variant) = variant else {
                            panic!(
                                "For type {name} with inhabited variant {var_id} expected a layout"
                            );
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
                                    // Find the smallest value not in the used set.
                                    let candidate = (0..).find(|v| !used_vals.contains(v)).unwrap();
                                    IntegerValue::from_bits(int_ty, candidate)
                                }))
                        });
                        assert_eq!(
                            Ok(var_id),
                            result,
                            "For type {name} variant {var_id}, tagger = {tagger:?}",
                        );
                    }
                    None => (),
                }
            }
        }
    }
    Ok(())
}

#[test]
fn print_layouts() -> anyhow::Result<()> {
    let crate_data = translate_rust_text(CRATE_SOURCE, &[])?;
    let the_target = crate_data.target_information.keys().next().unwrap().clone();
    assert_eq!(
        crate_data.target_information[&the_target].c_enum_smallest_repr_ty,
        IntTy::I32,
    );

    // Collect and print all layouts.
    let mut layouts_str = String::new();
    for tdecl in crate_data.type_decls.iter() {
        // Skips the builtin ADTs too, whose names start with a `PathElem::Builtin`.
        let is_local = matches!(
            tdecl.item_meta.name.name.first().and_then(|e| e.as_ident()),
            Some((crate_name, _)) if crate_name == "test_crate"
        );
        if !is_local {
            continue;
        }
        let ctx = FmtCtx {
            translated: Some(&crate_data),
            generics: BindingStack::new(Cow::Borrowed(&tdecl.generics)),
            indent_level: 1,
            ..Default::default()
        };
        let td_id = if let Some(aliased) = tdecl.kind.as_alias()
            && let Some(aliased_id) = aliased.as_adt_id()
        {
            aliased_id
        } else {
            tdecl.def_id
        };
        let layout_ctx = TypeDeclFmtCtx {
            fmt: &ctx,
            ty_decl_id: td_id,
        };
        let name = tdecl.item_meta.name.debug_repr(&crate_data);
        writeln!(&mut layouts_str, "{name}")?;
        let opt_layout = tdecl.layout.get(&the_target).cloned();
        if let Some(layout) = opt_layout {
            write!(&mut layouts_str, "{}", layout.with_ctx(&layout_ctx))?;
        }
        writeln!(&mut layouts_str)?;
    }
    compare_or_overwrite(layouts_str, &PathBuf::from("./tests/layout.txt"))?;

    Ok(())
}

#[test]
fn layout_guarantee_concretize_check() -> anyhow::Result<()> {
    let crate_data = translate_rust_text(CRATE_SOURCE, &[])?;
    let the_target = crate_data.target_information.keys().next().unwrap().clone();
    assert_eq!(
        crate_data.target_information[&the_target].c_enum_smallest_repr_ty,
        IntTy::I32,
    );

    fn byte_count_eq_scalar(byte_count: ByteCount, scalar: IntegerValue, ctx: String) {
        if scalar.is_signed() {
            assert_eq!(byte_count as i128, *scalar.as_signed().unwrap().1, "{ctx}");
        } else {
            assert_eq!(
                byte_count as u128,
                *scalar.as_unsigned().unwrap().1,
                "{ctx}"
            );
        }
    }

    // Compute and concretize layout guarantees and check them against the actual layouts.
    // Also, print all stages.
    let mut layout_computer = LayoutGuaranteeHelper::new(&crate_data, &the_target);
    let mut buffer = String::new();
    for tdecl in crate_data.type_decls.iter() {
        let is_local = matches!(
            tdecl.item_meta.name.name.first().and_then(|e| e.as_ident()),
            Some((crate_name, _)) if crate_name == "test_crate"
        );
        if !is_local {
            continue;
        }
        let ctx = FmtCtx {
            translated: Some(&crate_data),
            generics: BindingStack::new(Cow::Borrowed(&tdecl.generics)),
            indent_level: 1,
            ..Default::default()
        };
        let td_id = if let Some(aliased) = tdecl.kind.as_alias()
            && let Some(aliased_id) = aliased.as_adt_id()
        {
            aliased_id
        } else {
            tdecl.def_id
        };
        let layout_ctx = TypeDeclFmtCtx {
            fmt: &ctx,
            ty_decl_id: td_id,
        };
        let name = tdecl.item_meta.name.debug_repr(&crate_data);
        writeln!(&mut buffer, "{name}")?;
        let fake_ty = Ty::new(TyKind::Adt(TypeDeclRef {
            id: tdecl.def_id,
            generics: Box::new(tdecl.generics.identity_args()),
            builtin: None,
        }));

        let opt_concretized = layout_computer.compute_concrete_layout_guarantees(fake_ty.clone());
        // Check whether concretized layout guarantees always match known layouts.
        if let Some(layout) = tdecl.layout.get(&the_target)
            && let Some(guarantees) = &opt_concretized
            && let Some(size) = layout.size.chosen
            && let Some(align) = layout.align.chosen
        {
            if let Some(constant) = guarantees.size.as_constant()
                && let ConstantExprKind::Integer(size_guarantee) = constant.kind()
            {
                byte_count_eq_scalar(size, *size_guarantee, format!("{name}.size"));
            }
            if let Some(constant) = guarantees.align.as_constant()
                && let ConstantExprKind::Integer(align_guarantee) = constant.kind()
            {
                byte_count_eq_scalar(align, *align_guarantee, format!("{name}.align"));
            }

            for (v_id, variant) in layout.variant_layouts.iter_enumerated() {
                if let Some(variant) = variant {
                    for (f_id, offset) in variant.field_offsets.iter_enumerated() {
                        if let Some(offset_guarantee) =
                            layout_computer.lookup_pre_computed_offset(&fake_ty, Some(v_id), f_id)
                            && let Some(constant) = offset_guarantee.as_constant()
                            && let ConstantExprKind::Integer(s) = constant.kind()
                            && let Some(offset) = offset.chosen
                        {
                            byte_count_eq_scalar(offset, *s, format!("{name}.{v_id}.{f_id}"));
                        }
                    }
                }
            }
        }

        let tdr = fake_ty.as_adt().unwrap();
        if let Some(l) = tdecl.layout.get(&the_target) {
            if let Some(g) = LayoutGuarantees::for_type_decl(tdr, &tdecl.kind, &crate_data, &l.repr)
            {
                write!(&mut buffer, "direct {}", g.with_ctx(&layout_ctx))?;
            }
            write!(
                &mut buffer,
                "stored {}",
                LayoutGuarantees::from_layout(l)
                    .unwrap()
                    .with_ctx(&layout_ctx)
            )?;
        }
        if let Some(l) = opt_concretized {
            write!(&mut buffer, "normalized {}", l.with_ctx(&layout_ctx))?;
        }
        writeln!(&mut buffer)?;
    }

    compare_or_overwrite(buffer, &PathBuf::from("./tests/layout_guarantees.txt"))?;
    Ok(())
}
