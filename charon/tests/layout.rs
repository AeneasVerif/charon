use itertools::Itertools;
use std::{fmt::Write, path::PathBuf};

use charon_lib::ast::*;
use charon_lib::{
    formatter::{AstFormatter, IntoFormatter},
    pretty::FmtWithCtx,
};

mod util;
use util::*;

fn eval_size_expr(expr: &SizeExpr, dyn_size: u128, dyn_align: u128, slice_length: u128) -> u128 {
    match expr.kind() {
        SizeExprKind::Constant(constant) => constant
            .as_usize_literal()
            .expect("chosen size expressions must only contain integer constants"),
        SizeExprKind::FromMetadata(metadata) => match metadata {
            MetadataValue::DynSize => dyn_size,
            MetadataValue::DynAlign => dyn_align,
            MetadataValue::SliceLength => slice_length,
        },
        SizeExprKind::Max(values) => values
            .iter()
            .map(|value| eval_size_expr(value, dyn_size, dyn_align, slice_length))
            .max()
            .unwrap(),
        SizeExprKind::Min(values) => values
            .iter()
            .map(|value| eval_size_expr(value, dyn_size, dyn_align, slice_length))
            .min()
            .unwrap(),
        SizeExprKind::Plus(left, right) => {
            eval_size_expr(left, dyn_size, dyn_align, slice_length)
                + eval_size_expr(right, dyn_size, dyn_align, slice_length)
        }
        SizeExprKind::Scale(base, multiplier) => {
            eval_size_expr(base, dyn_size, dyn_align, slice_length)
                * multiplier
                    .as_usize_literal()
                    .expect("chosen size expressions must only contain integer constants")
        }
        SizeExprKind::AlignTo { base, target_align } => {
            let base = eval_size_expr(base, dyn_size, dyn_align, slice_length);
            let align = eval_size_expr(target_align, dyn_size, dyn_align, slice_length);
            base.next_multiple_of(align)
        }
        SizeExprKind::AtLeast(_) | SizeExprKind::IfInhabited { .. } => {
            panic!("chosen size expressions must be exact")
        }
    }
}

#[test]
fn type_layout() -> anyhow::Result<()> {
    let crate_data = translate_rust_file("tests/ui/layout_examples.rs", &[])?;

    // Check whether discriminator/tagger roundtrips are correct: use each variant's tagger
    // to answer the discriminator's read queries, and verify we get back the same variant.
    let the_target = crate_data.target_information.keys().next().unwrap().clone();
    assert_eq!(
        crate_data.target_information[&the_target].c_enum_smallest_repr_ty,
        IntTy::I32,
    );
    let ptr_size = u128::from(crate_data.target_information[&the_target].target_pointer_size);
    for tdecl in crate_data.type_decls.iter() {
        if let Some(layout) = tdecl.layout.get(&the_target)
            && let Some(discriminator) = &layout.discriminator
        {
            let name = tdecl.item_meta.name.debug_repr(&crate_data);
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
            }
        }
    }

    let local_layout = |name: &str| {
        crate_data
            .type_decls
            .iter()
            .find(|decl| decl.item_meta.name.debug_repr(&crate_data) == name)
            .unwrap()
            .layout
            .get(&the_target)
            .unwrap()
    };
    let assert_chosen = |name: &str, metadata: (u128, u128, u128), expected: (u128, u128)| {
        let layout = local_layout(name);
        assert_eq!(
            (
                eval_size_expr(&layout.size.chosen, metadata.0, metadata.1, metadata.2),
                eval_size_expr(&layout.align.chosen, metadata.0, metadata.1, metadata.2),
            ),
            expected,
        );
    };
    assert_chosen(
        "test_crate::UnsizedStruct",
        (0, 0, 3),
        (4 * ptr_size, ptr_size),
    );
    assert_chosen("test_crate::UnsizedDyn", (12, 4, 0), (16, 4));
    assert_chosen(
        "test_crate::NestedUnsized",
        (0, 0, 3),
        (5 * ptr_size, ptr_size),
    );
    assert_chosen("test_crate::PackedUnsized", (0, 0, 3), (14, 2));

    let mut layouts = String::new();
    let fmt = (&crate_data).into_fmt();
    for tdecl in crate_data.type_decls.iter() {
        // Skips the builtin ADTs too, whose names start with a `PathElem::Builtin`.
        let is_local = matches!(
            tdecl.item_meta.name.name.first().and_then(|e| e.as_ident()),
            Some((crate_name, _)) if crate_name == "test_crate"
        );
        if !is_local {
            continue;
        }

        if !layouts.is_empty() {
            writeln!(layouts)?;
        }
        let name = tdecl.item_meta.name.debug_repr(&crate_data);
        writeln!(layouts, "{name}:")?;
        match tdecl.layout.get(&the_target) {
            Some(layout) => {
                let fmt = fmt.set_generics(&tdecl.generics);
                let fmt = fmt.set_current_type(tdecl.def_id);
                for line in layout.to_string_with_ctx(&fmt).lines() {
                    writeln!(layouts, "  {line}")?;
                }
            }
            None => writeln!(layouts, "  none")?,
        }
    }

    compare_or_overwrite(layouts, &PathBuf::from("./tests/layout.txt"))?;
    Ok(())
}
