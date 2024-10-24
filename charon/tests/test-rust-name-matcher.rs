#![feature(rustc_private)]
use charon_lib::formatter::IntoFormatter;
use charon_lib::pretty::FmtWithCtx;
use itertools::Itertools;

use charon_lib::ast::*;
use charon_lib::name_matcher::Pattern;

mod util;

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

#[test]
fn test_name_matcher() -> anyhow::Result<()> {
    let crate_data = util::translate_rust_text(
        r#"
        #![feature(register_tool)]
        #![register_tool(pattern)]
        mod foo {
            #[pattern::fail("test_crate::foo::bar::_")]
            #[pattern::pass("test_crate::foo::bar")]
            #[pattern::pass("test_crate::foo::_")]
            #[pattern::pass("test_crate::foo")]
            #[pattern::pass("test_crate")]
            #[pattern::pass("test_crate::_")]
            #[pattern::pass("test_crate::_::bar")]
            #[pattern::fail("test_crate::_::lsdkfjs")]
            #[pattern::pass("crate::foo::bar")]
            #[pattern::fail("foo::bar")]
            fn bar() {}
        }

        #[pattern::pass("test_crate::Trait")]
        #[pattern::fail("test_crate::Trait<_>")]
        #[pattern::fail("test_crate::Trait<_, _>")]
        trait Trait<T> {
            #[pattern::pass("test_crate::Trait::method")]
            #[pattern::fail("test_crate::Trait<_>::method")]
            fn method<U>();
        }

        #[pattern::pass("test_crate::{impl test_crate::Trait<_> for _}")]
        #[pattern::pass("test_crate::{impl test_crate::Trait<_, _>}")]
        #[pattern::fail("test_crate::{impl test_crate::Trait<_, _> for _}")]
        #[pattern::pass("test_crate::{impl test_crate::Trait<core::option::Option<_>> for alloc::boxed::Box<_>}")]
        #[pattern::pass("test_crate::{impl test_crate::Trait<alloc::boxed::Box<_>, core::option::Option<_>>}")]
        #[pattern::pass("test_crate::{impl test_crate::Trait<core::option::Option<_>> for alloc::boxed::Box<_>}")]
        #[pattern::fail("test_crate::{impl test_crate::Trait<Option<_>> for alloc::boxed::Box<_>}")]
        #[pattern::fail("test_crate::{impl test_crate::Trait<FooBar<_>> for alloc::boxed::Box<_>}")]
        #[pattern::fail("test_crate::{impl test_crate::Trait<core::option::Option<_>> for FooBar<_>}")]
        #[pattern::fail("test_crate::{impl Trait<_> for _}")]
        #[pattern::fail("test_crate::{impl test_crate::OtherTrait<_> for _}")]
        #[pattern::fail("test_crate::Trait<_>")]
        impl<T> Trait<Option<T>> for Box<T> {
            #[pattern::pass("test_crate::{impl test_crate::Trait<_> for _}::method")]
            #[pattern::pass("test_crate::{impl test_crate::Trait<_> for _}::_")]
            #[pattern::pass("test_crate::{impl test_crate::Trait<_> for _}")]
            #[pattern::pass("test_crate::{impl test_crate::Trait<_, _>}"::method)]
            #[pattern::fail("test_crate::Trait<_>::method")]
            fn method<U>() {}
        }

        #[pattern::pass("test_crate::{impl test_crate::Trait<_> for Slice<_>}")]
        impl<T> Trait<T> for [T] {
            fn method<U>() {}
        }

        #[pattern::pass("test_crate::{impl test_crate::Trait<_> for &Slice<_>}")]
        impl<T> Trait<T> for &[T] {
            fn method<U>() {}
        }
        "#,
    )?;
    let fmt_ctx = &crate_data.into_fmt();

    for item in crate_data.all_items() {
        let name = &item.item_meta().name;
        let patterns = item
            .item_meta()
            .attr_info
            .attributes
            .iter()
            .filter_map(|a| parse_pattern_attr(a))
            .collect_vec();
        for (pass, pat) in patterns {
            let passes = pat.matches(&crate_data, name);
            if passes != pass {
                if passes {
                    panic!(
                        "Pattern `{pat}` passes on `{}` but shouldn't",
                        name.fmt_with_ctx(fmt_ctx)
                    );
                } else {
                    panic!(
                        "Pattern `{pat}` doesn't pass on `{}` but should",
                        name.fmt_with_ctx(fmt_ctx)
                    );
                }
            }
        }
    }

    Ok(())
}
