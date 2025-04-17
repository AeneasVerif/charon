//! Machinery to resolve a string path into a `DefId`. Based on `clippy_utils::def_path_res`.
use itertools::Itertools;
use rustc_ast::Mutability;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId, LocalDefId, LOCAL_CRATE};
use rustc_hir::{ImplItemRef, ItemKind, Node, OwnerId, TraitItemRef};
use rustc_middle::ty::{fast_reject::SimplifiedType, FloatTy, IntTy, TyCtxt, UintTy};
use rustc_span::symbol::{Ident, Symbol};

fn find_primitive_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
) -> impl Iterator<Item = DefId> + use<'tcx> {
    let ty = match name {
        "bool" => SimplifiedType::Bool,
        "char" => SimplifiedType::Char,
        "str" => SimplifiedType::Str,
        "array" => SimplifiedType::Array,
        "slice" => SimplifiedType::Slice,
        // FIXME: rustdoc documents these two using just `pointer`.
        //
        // Maybe this is something we should do here too.
        "const_ptr" => SimplifiedType::Ptr(Mutability::Not),
        "mut_ptr" => SimplifiedType::Ptr(Mutability::Mut),
        "isize" => SimplifiedType::Int(IntTy::Isize),
        "i8" => SimplifiedType::Int(IntTy::I8),
        "i16" => SimplifiedType::Int(IntTy::I16),
        "i32" => SimplifiedType::Int(IntTy::I32),
        "i64" => SimplifiedType::Int(IntTy::I64),
        "i128" => SimplifiedType::Int(IntTy::I128),
        "usize" => SimplifiedType::Uint(UintTy::Usize),
        "u8" => SimplifiedType::Uint(UintTy::U8),
        "u16" => SimplifiedType::Uint(UintTy::U16),
        "u32" => SimplifiedType::Uint(UintTy::U32),
        "u64" => SimplifiedType::Uint(UintTy::U64),
        "u128" => SimplifiedType::Uint(UintTy::U128),
        "f32" => SimplifiedType::Float(FloatTy::F32),
        "f64" => SimplifiedType::Float(FloatTy::F64),
        _ => {
            return [].iter().copied();
        }
    };
    tcx.incoherent_impls(ty).iter().copied()
}

fn non_local_item_children_by_name(tcx: TyCtxt<'_>, def_id: DefId, name: Symbol) -> Vec<DefId> {
    match tcx.def_kind(def_id) {
        DefKind::Mod | DefKind::Enum | DefKind::Trait => tcx
            .module_children(def_id)
            .iter()
            .filter(|child| child.ident.name == name)
            .filter_map(|child| child.res.opt_def_id())
            .collect(),
        DefKind::Impl { .. } => tcx
            .associated_item_def_ids(def_id)
            .iter()
            .copied()
            .filter(|assoc_def_id| tcx.item_name(*assoc_def_id) == name)
            .collect(),
        _ => Vec::new(),
    }
}

fn local_item_children_by_name(tcx: TyCtxt<'_>, local_id: LocalDefId, name: Symbol) -> Vec<DefId> {
    let root_mod;
    let item_kind = match tcx.hir_node_by_def_id(local_id) {
        Node::Crate(r#mod) => {
            root_mod = ItemKind::Mod(Ident::dummy(), r#mod);
            &root_mod
        }
        Node::Item(item) => &item.kind,
        _ => return Vec::new(),
    };

    let res = |ident: Ident, owner_id: OwnerId| {
        if ident.name == name {
            Some(owner_id.to_def_id())
        } else {
            None
        }
    };

    match item_kind {
        ItemKind::Mod(_, r#mod) => r#mod
            .item_ids
            .iter()
            .filter_map(|&item_id| {
                let ident = tcx.hir_item(item_id).kind.ident()?;
                res(ident, item_id.owner_id)
            })
            .collect(),
        ItemKind::Impl(r#impl) => r#impl
            .items
            .iter()
            .filter_map(|&ImplItemRef { ident, id, .. }| res(ident, id.owner_id))
            .collect(),
        ItemKind::Trait(.., trait_item_refs) => trait_item_refs
            .iter()
            .filter_map(|&TraitItemRef { ident, id, .. }| res(ident, id.owner_id))
            .collect(),
        _ => Vec::new(),
    }
}

fn item_children_by_name(tcx: TyCtxt<'_>, def_id: DefId, name: Symbol) -> Vec<DefId> {
    if let Some(local_id) = def_id.as_local() {
        local_item_children_by_name(tcx, local_id, name)
    } else {
        non_local_item_children_by_name(tcx, def_id, name)
    }
}

/// Resolves a def path like `std::vec::Vec`.
///
/// Can return multiple resolutions when there are multiple versions of the same crate, e.g.
/// `memchr::memchr` could return the functions from both memchr 1.0 and memchr 2.0.
///
/// Also returns multiple results when there are multiple paths under the same name e.g. `std::vec`
/// would have both a [`DefKind::Mod`] and [`DefKind::Macro`].
///
/// This function is expensive and should be used sparingly.
///
/// If the path does not correspond to an existing item, return the first subpath that doesn't
/// correspond to an item.
pub fn def_path_def_ids<'a>(
    tcx: TyCtxt<'_>,
    path: &'a [&'a str],
) -> Result<Vec<DefId>, &'a [&'a str]> {
    let mut items = vec![];
    for (i, &segment_str) in path.iter().enumerate() {
        let segment = Symbol::intern(segment_str);
        if i == 0 {
            items = tcx
                .crates(())
                .iter()
                .copied()
                .chain([LOCAL_CRATE])
                .filter(move |&num| tcx.crate_name(num) == segment)
                // Also consider "crate" a valid name for the local crate.
                .chain(if segment_str == "crate" {
                    Some(LOCAL_CRATE)
                } else {
                    None
                })
                .map(CrateNum::as_def_id)
                .collect_vec();
            items.extend(find_primitive_impls(tcx, segment_str));
        } else {
            items = items
                .into_iter()
                .flat_map(|def_id| {
                    // When the current def_id is e.g. `struct S`, check the impl items in `impl S {
                    // ... }`
                    let inherent_impl_children = tcx
                        .inherent_impls(def_id)
                        .iter()
                        .flat_map(|&impl_def_id| item_children_by_name(tcx, impl_def_id, segment));

                    let direct_children = item_children_by_name(tcx, def_id, segment);

                    inherent_impl_children.chain(direct_children)
                })
                .collect();
        }
        if items.is_empty() {
            return Err(&path[..=i]);
        }
    }
    Ok(items)
}
