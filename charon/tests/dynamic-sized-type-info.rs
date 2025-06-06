use std::path::PathBuf;

use charon_lib::ast::*;

mod util;
use indexmap::IndexMap;
use util::*;

#[test]
fn dst_meta_kind() -> anyhow::Result<()> {
  let crate_data = translate_rust_text(
    r#"
    type Alias = str;
    struct StrDst {
      meta : i32,
      str : str
    }

    struct SliceDst {
      meta : u64,
      slice : [u8]
    }

    struct Point { x : i32, y : u32, z : i128 }
    struct MoreSliceDst {
      meta : u128,
      slice : [Point]
    }

    struct Embedded {
      meta : i32,
      more : MoreSliceDst
    }

    trait Showable { fn show(&self) -> &str; }
    struct DynTrait {
      meta : u32,
      dynt : dyn Showable
    }
    "#
  )?;
  let meta_kinds : IndexMap<String, Option<DstMetaKind>> = crate_data
    .type_decls
    .iter()
    .filter_map(|td| {
      if td.item_meta.name.name[0].as_ident().unwrap().0 != "test_crate" {
          return None;
      }
      let name = repr_name(&crate_data, &td.item_meta.name);
      Some((name, td.dst_meta_kind.clone()))
    })
    .collect();
  let str = serde_json::to_string_pretty(&meta_kinds)?;
  
  let action = if std::env::var("IN_CI").as_deref() == Ok("1") {
      Action::Verify
  } else {
      Action::Overwrite
  };
  compare_or_overwrite(action, str, &PathBuf::from("./tests/dst-meta-kinds.json"))?;
  Ok(())
}