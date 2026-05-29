use charon_lib::formatter::IntoFormatter;
use charon_lib::pretty::FmtWithCtx;
use itertools::Itertools;

use charon_lib::ast::*;
use charon_lib::name_matcher::Pattern;

mod util;

static TEST_FILE: &str = "tests/ui/rust-name-matcher-tests.rs";

fn parse_pattern_attr(a: &Attribute) -> Option<(bool, Pattern)> {
    let Attribute::Unknown(a) = a else {
        return None;
    };
    let (pass, a) = if a.path == "pattern::pass" {
        (true, a)
    } else if a.path == "pattern::fail" {
        (false, a)
    } else {
        return None;
    };
    let a = a.args.as_ref()?;
    let a = a.strip_prefix("\"")?.strip_suffix("\"")?;
    match Pattern::parse(a) {
        Ok(pat) => Some((pass, pat)),
        Err(e) => {
            panic!("Failed to parse pattern `{a}` ({e})")
        }
    }
}

fn test_crate_data(crate_data: &TranslatedCrate) -> anyhow::Result<()> {
    let fmt_ctx = &crate_data.into_fmt();

    for item in crate_data.all_items() {
        let name = &item.item_meta().name;
        let patterns = item
            .item_meta()
            .attr_info
            .attributes
            .iter()
            .filter_map(parse_pattern_attr)
            .collect_vec();
        for (pass, pat) in patterns {
            let passes = pat.matches_item(crate_data, item);
            if passes != pass {
                if passes {
                    panic!(
                        "Pattern `{pat}` passes on `{}` but shouldn't",
                        name.with_ctx(fmt_ctx)
                    );
                } else {
                    panic!(
                        "Pattern `{pat}` doesn't pass on `{}` but should",
                        name.with_ctx(fmt_ctx)
                    );
                }
            }
        }
    }

    Ok(())
}

#[test]
fn test_partial_mono_name_matcher() -> anyhow::Result<()> {
    let code = r#"
        fn identity<T>(x: T) -> T {
            x
        }

        fn use_id_mut<A, B>(mut x: A, mut y: B) {
            let _ = identity(&mut x);
            let _ = identity(Some(&mut x));
            let _ = identity((&mut x, &mut y));
        }
    "#;
    let crate_data = util::translate_rust_text(
        code,
        &[
            "--monomorphize-mut=except-types",
            "--remove-adt-clauses",
            "--remove-associated-types=*",
        ],
    )?;

    let identity_instantiations = crate_data.fun_decls.iter().filter(|decl| {
        let name = &decl.item_meta.name.name;
        matches!(
            name.as_slice(),
            [.., PathElem::Ident(ident, _), PathElem::Instantiated(_)] if ident == "identity"
        )
    });
    let ref_pat = Pattern::parse("test_crate::identity<&mut _>").unwrap();
    let option_ref_pat =
        Pattern::parse("test_crate::identity<core::option::Option<&mut _>>").unwrap();
    let mut_ref_tuple_instantiation = |decl: &FunDecl| {
        let [
            ..,
            PathElem::Ident(ident, _),
            PathElem::Instantiated(instantiation),
        ] = decl.item_meta.name.name.as_slice()
        else {
            return false;
        };
        if ident != "identity" {
            return false;
        }
        let Ok(ty) = instantiation.skip_binder.types.iter().exactly_one() else {
            return false;
        };
        let Some(fields) = ty.as_tuple() else {
            return false;
        };
        fields.len() == 2
            && fields
                .iter()
                .all(|field| matches!(field.kind(), TyKind::Ref(_, _, RefKind::Mut)))
    };
    let matched = identity_instantiations
        .map(|decl| {
            let item = ItemRef::Fun(decl);
            (
                ref_pat.matches_item(&crate_data, item),
                option_ref_pat.matches_item(&crate_data, item),
                mut_ref_tuple_instantiation(decl),
            )
        })
        .fold((false, false, false), |acc, matched| {
            (acc.0 || matched.0, acc.1 || matched.1, acc.2 || matched.2)
        });

    assert!(
        matched.0,
        "no partial-monomorphized `identity<&mut _>` matched"
    );
    assert!(
        matched.1,
        "no partial-monomorphized `identity<Option<&mut _>>` matched"
    );
    assert!(
        matched.2,
        "no partial-monomorphized `identity<(&mut _, &mut _)>` matched"
    );

    Ok(())
}

#[test]
fn test_name_matcher() -> anyhow::Result<()> {
    let code = &std::fs::read_to_string(TEST_FILE)?;
    let crate_data = util::translate_rust_text(code, &[])?;
    test_crate_data(&crate_data)?;
    let mono_crate_data = util::translate_rust_text(code, &["--monomorphize"])?;
    test_crate_data(&mono_crate_data)
}
