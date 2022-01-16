use crate::common::*;
use crate::im_ast as ast;
use crate::register::RegisteredDeclarations;
use crate::reorder_decls as rd;
use crate::types as ty;
use macros::{VariantIndexArity, VariantName};
use rustc_hir::def_id::DefId;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::collections::HashMap;
use std::fmt::{Debug, Display, Error, Formatter};
use std::vec::Vec;

pub type GDeclarationGroup<Id> = rd::GDeclarationGroup<Id>;
pub type TypeDeclarationGroup = rd::GDeclarationGroup<ty::TypeDefId::Id>;
pub type FunDeclarationGroup = rd::GDeclarationGroup<ast::FunDefId::Id>;
pub type DeclarationGroup = rd::DeclarationGroup<ty::TypeDefId::Id, ast::FunDefId::Id>;

pub struct OrderedDecls {
    /// The properly grouped and ordered declarations
    pub decls: Vec<DeclarationGroup>,
    /// Rust type identifiers to translation identifiers
    pub type_rid_to_id: HashMap<DefId, ty::TypeDefId::Id>,
    /// Translation type identifiers to rust identifiers
    pub type_id_to_rid: HashMap<ty::TypeDefId::Id, DefId>,
    /// Rust function identifiers to translation identifiers
    pub fun_rid_to_id: HashMap<DefId, ast::FunDefId::Id>,
    /// Translation function identifiers to rust identifiers
    pub fun_id_to_rid: HashMap<ast::FunDefId::Id, DefId>,
}

/// Convert the definition ids used by the rust compiler to our own definition
/// ids.
pub fn rust_to_local_ids(reordered: &rd::DeclarationsGroups<DefId, DefId>) -> OrderedDecls {
    let mut type_rid_to_id: HashMap<DefId, ty::TypeDefId::Id> = HashMap::new();
    let mut fun_rid_to_id: HashMap<DefId, ast::FunDefId::Id> = HashMap::new();
    let mut type_id_to_rid: HashMap<ty::TypeDefId::Id, DefId> = HashMap::new();
    let mut fun_id_to_rid: HashMap<ast::FunDefId::Id, DefId> = HashMap::new();

    let mut type_counter = ty::TypeDefId::Generator::new();
    let mut fun_counter = ast::FunDefId::Generator::new();

    let mut decls: Vec<DeclarationGroup> = Vec::new();

    // Compute the translated list of declarations and the mappings from rust
    // identifiers to translation identifiers and vice-versa.
    for decl in &reordered.decls {
        match decl {
            rd::DeclarationGroup::Type(rd::GDeclarationGroup::NonRec(rid)) => {
                let id = type_counter.fresh_id();
                type_rid_to_id.insert(*rid, id);
                type_id_to_rid.insert(id, *rid);
                decls.push(DeclarationGroup::Type(GDeclarationGroup::NonRec(id)));
            }
            rd::DeclarationGroup::Type(rd::GDeclarationGroup::Rec(rids)) => {
                let mut ids: Vec<ty::TypeDefId::Id> = Vec::new();
                for rid in rids {
                    let id = type_counter.fresh_id();
                    type_rid_to_id.insert(*rid, id);
                    type_id_to_rid.insert(id, *rid);
                    ids.push(id);
                }

                decls.push(DeclarationGroup::Type(GDeclarationGroup::Rec(ids)));
            }
            rd::DeclarationGroup::Fun(rd::GDeclarationGroup::NonRec(rid)) => {
                let id = fun_counter.fresh_id();
                fun_rid_to_id.insert(*rid, id);
                fun_id_to_rid.insert(id, *rid);
                decls.push(DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)));
            }
            rd::DeclarationGroup::Fun(rd::GDeclarationGroup::Rec(rids)) => {
                let mut ids: Vec<ast::FunDefId::Id> = Vec::new();
                for rid in rids {
                    let id = fun_counter.fresh_id();
                    fun_rid_to_id.insert(*rid, id);
                    fun_id_to_rid.insert(id, *rid);
                    ids.push(id);
                }

                decls.push(DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)));
            }
        }
    }

    // Return
    OrderedDecls {
        decls,
        type_rid_to_id,
        fun_rid_to_id,
        type_id_to_rid,
        fun_id_to_rid,
    }
}
