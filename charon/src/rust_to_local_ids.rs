#![allow(dead_code)]
use crate::im_ast as ast;
use crate::reorder_decls as rd;
use crate::types as ty;
use rustc_hir::def_id::DefId;
use std::collections::{HashMap, HashSet};
use std::vec::Vec;

pub type GDeclarationGroup<Id> = rd::GDeclarationGroup<Id>;
pub type TypeDeclarationGroup = rd::GDeclarationGroup<ty::TypeDeclId::Id>;
pub type FunDeclarationGroup = rd::GDeclarationGroup<ast::FunDeclId::Id>;
pub type DeclarationGroup =
    rd::DeclarationGroup<ty::TypeDeclId::Id, ast::FunDeclId::Id, ast::ConstDeclId::Id>;

pub struct OrderedDecls {
    /// The properly grouped and ordered declarations
    pub decls: Vec<DeclarationGroup>,
    /// The opaque type ids
    pub opaque_types: HashSet<ty::TypeDeclId::Id>,
    /// The opaque fun ids
    pub opaque_funs: HashSet<ast::FunDeclId::Id>,
    /// The opaque const ids
    pub opaque_consts: HashSet<ast::ConstDeclId::Id>,
    /// Rust type identifiers to translation identifiers
    pub type_rid_to_id: HashMap<DefId, ty::TypeDeclId::Id>,
    /// Translation type identifiers to rust identifiers
    pub type_id_to_rid: HashMap<ty::TypeDeclId::Id, DefId>,
    /// Rust function identifiers to translation identifiers
    pub fun_rid_to_id: HashMap<DefId, ast::FunDeclId::Id>,
    /// Translation function identifiers to rust identifiers
    pub fun_id_to_rid: HashMap<ast::FunDeclId::Id, DefId>,
    /// Rust constant identifiers to translation identifiers
    pub const_rid_to_id: HashMap<DefId, ast::ConstDeclId::Id>,
    /// Translation constant identifiers to rust identifiers
    pub const_id_to_rid: HashMap<ast::ConstDeclId::Id, DefId>,
}

/// Convert the definition ids used by the rust compiler to our own definition
/// ids.
pub fn rust_to_local_ids(reordered: &rd::DeclarationsGroups<DefId, DefId, DefId>) -> OrderedDecls {
    let mut opaque_types = HashSet::new();
    let mut opaque_funs = HashSet::new();
    let mut opaque_consts = HashSet::new();

    let mut type_rid_to_id: HashMap<DefId, ty::TypeDeclId::Id> = HashMap::new();
    let mut fun_rid_to_id: HashMap<DefId, ast::FunDeclId::Id> = HashMap::new();
    let mut const_rid_to_id: HashMap<DefId, ast::ConstDeclId::Id> = HashMap::new();

    let mut type_id_to_rid: HashMap<ty::TypeDeclId::Id, DefId> = HashMap::new();
    let mut fun_id_to_rid: HashMap<ast::FunDeclId::Id, DefId> = HashMap::new();
    let mut const_id_to_rid: HashMap<ast::ConstDeclId::Id, DefId> = HashMap::new();

    let mut type_counter = ty::TypeDeclId::Generator::new();
    let mut fun_counter = ast::FunDeclId::Generator::new();
    let mut const_counter = ast::ConstDeclId::Generator::new();

    let mut decls: Vec<DeclarationGroup> = Vec::new();

    // Compute the translated list of declarations and the mappings from rust
    // identifiers to translation identifiers and vice-versa.
    for decl in &reordered.decls {
        match decl {
            rd::DeclarationGroup::Type(rd::GDeclarationGroup::NonRec(rid)) => {
                let id = type_counter.fresh_id();
                type_rid_to_id.insert(*rid, id);
                type_id_to_rid.insert(id, *rid);
                if reordered.external_type_ids.contains(rid) {
                    opaque_types.insert(id);
                }
                decls.push(DeclarationGroup::Type(GDeclarationGroup::NonRec(id)));
            }
            rd::DeclarationGroup::Type(rd::GDeclarationGroup::Rec(rids)) => {
                let mut ids: Vec<ty::TypeDeclId::Id> = Vec::new();
                for rid in rids {
                    let id = type_counter.fresh_id();
                    type_rid_to_id.insert(*rid, id);
                    type_id_to_rid.insert(id, *rid);
                    if reordered.external_type_ids.contains(rid) {
                        opaque_types.insert(id);
                    }
                    ids.push(id);
                }

                decls.push(DeclarationGroup::Type(GDeclarationGroup::Rec(ids)));
            }
            rd::DeclarationGroup::Fun(rd::GDeclarationGroup::NonRec(rid)) => {
                let id = fun_counter.fresh_id();
                fun_rid_to_id.insert(*rid, id);
                fun_id_to_rid.insert(id, *rid);
                if reordered.external_fun_ids.contains(rid) {
                    opaque_funs.insert(id);
                }
                decls.push(DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)));
            }
            rd::DeclarationGroup::Fun(rd::GDeclarationGroup::Rec(rids)) => {
                let mut ids: Vec<ast::FunDeclId::Id> = Vec::new();
                for rid in rids {
                    let id = fun_counter.fresh_id();
                    fun_rid_to_id.insert(*rid, id);
                    fun_id_to_rid.insert(id, *rid);
                    if reordered.external_fun_ids.contains(rid) {
                        opaque_funs.insert(id);
                    }
                    ids.push(id);
                }

                decls.push(DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)));
            }
            rd::DeclarationGroup::Const(rd::GDeclarationGroup::NonRec(rid)) => {
                let id = const_counter.fresh_id();
                const_rid_to_id.insert(*rid, id);
                const_id_to_rid.insert(id, *rid);
                if reordered.external_const_ids.contains(rid) {
                    opaque_consts.insert(id);
                }
                decls.push(DeclarationGroup::Const(GDeclarationGroup::NonRec(id)));
            }
            rd::DeclarationGroup::Const(rd::GDeclarationGroup::Rec(rids)) => {
                let mut ids: Vec<ast::ConstDeclId::Id> = Vec::new();
                for rid in rids {
                    let id = const_counter.fresh_id();
                    const_rid_to_id.insert(*rid, id);
                    const_id_to_rid.insert(id, *rid);
                    if reordered.external_const_ids.contains(rid) {
                        opaque_consts.insert(id);
                    }
                    ids.push(id);
                }

                decls.push(DeclarationGroup::Const(GDeclarationGroup::Rec(ids)));
            }
        }
    }

    // Return
    OrderedDecls {
        decls,
        opaque_types,
        opaque_funs,
        opaque_consts,
        type_rid_to_id,
        fun_rid_to_id,
        const_rid_to_id,
        type_id_to_rid,
        fun_id_to_rid,
        const_id_to_rid,
    }
}
