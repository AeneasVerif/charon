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
        "#,
    )?;
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
