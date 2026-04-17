use charon_lib::ast::*;
use convert_case::{Case, Casing};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use crate::GenerateCtx;

/// `Name` is a complex datastructure; to inspect it we serialize it a little bit.
pub fn repr_name(n: &Name) -> String {
    n.name
        .iter()
        .map(|path_elem| match path_elem {
            PathElem::Ident(i, _) => i.clone(),
            PathElem::Impl(..) => "<impl>".to_string(),
            PathElem::Instantiated(..) => "<mono>".to_string(),
            PathElem::Target(target) => target.clone(),
        })
        .join("::")
}

pub fn make_ocaml_ident(name: &str) -> String {
    let mut name = name.to_case(Case::Snake);
    if matches!(
        &*name,
        "assert"
            | "bool"
            | "char"
            | "end"
            | "float"
            | "fun"
            | "function"
            | "include"
            | "let"
            | "method"
            | "open"
            | "rec"
            | "struct"
            | "to"
            | "type"
            | "virtual"
    ) {
        name += "_";
    }
    name
}

impl<'a> GenerateCtx<'a> {
    pub fn id_from_name(&self, name: &str) -> TypeDeclId {
        self.name_to_type
            .get(name)
            .unwrap_or_else(|| panic!("Name not found: `{name}`"))
            .def_id
    }

    /// List the (recursive) children of this type.
    pub fn children_of(&self, name: &str) -> HashSet<TypeDeclId> {
        let start_id = self.id_from_name(name);
        self.children_of_inner(vec![start_id], |_| true)
    }

    /// List the (recursive) children of these types.
    pub fn children_of_many(&self, names: &[&str]) -> HashSet<TypeDeclId> {
        self.children_of_inner(
            names.iter().map(|name| self.id_from_name(name)).collect(),
            |_| true,
        )
    }

    pub fn children_of_inner(
        &self,
        ty: Vec<TypeDeclId>,
        explore: impl Fn(TypeDeclId) -> bool,
    ) -> HashSet<TypeDeclId> {
        let mut children = HashSet::new();
        let mut stack = ty.to_vec();
        while let Some(id) = stack.pop() {
            if !children.contains(&id)
                && explore(id)
                && self
                    .crate_data
                    .type_decls
                    .get(id)
                    .is_some_and(|decl| decl.item_meta.is_local)
            {
                children.insert(id);
                if let Some(contained) = self.type_tree.get(&id) {
                    stack.extend(contained);
                }
            }
        }
        children
    }

    /// Returns the OCaml identifier corresponding to this type,
    /// and the generated module name + short module name associated to it if
    /// they exist.
    pub fn type_to_ocaml_ident_raw(&self, td: &TypeDecl) -> (String, Option<(String, String)>) {
        let name = td
            .item_meta
            .attr_info
            .rename
            .as_ref()
            .unwrap_or(td.item_meta.name.name.last().unwrap().as_ident().unwrap().0);
        let module = self.ambiguous_types.get(&td.def_id);
        (make_ocaml_ident(name), module.cloned())
    }

    pub fn type_to_ocaml_ident(&self, td: &TypeDecl) -> String {
        let (name, module) = self.type_to_ocaml_ident_raw(td);
        match module {
            Some((module, _)) if self.current_module.as_ref().is_none_or(|m| m != &module) => {
                format!("{module}.{name}")
            }
            _ => name,
        }
    }

    /// Converts a type to the appropriate ocaml name. In case of generics, this provides appropriate
    /// parameters.
    pub fn type_to_ocaml_name(&self, ty: &Ty) -> String {
        match ty.kind() {
            TyKind::Literal(LiteralTy::Bool) => "bool".to_string(),
            TyKind::Literal(LiteralTy::Char) => "(Uchar.t [@visitors.opaque])".to_string(),
            TyKind::Literal(LiteralTy::Int(int_ty)) => match int_ty {
                // Even though OCaml ints are only 63 bits, only scalars with their 128 bits should be able to become too large
                IntTy::I128 => "big_int".to_string(),
                _ => "int".to_string(),
            },
            TyKind::Literal(LiteralTy::UInt(uint_ty)) => match uint_ty {
                // Even though OCaml ints are only 63 bits, only scalars with their 128 bits should be able to become too large
                UIntTy::U128 => "big_int".to_string(),
                _ => "int".to_string(),
            },
            TyKind::Literal(LiteralTy::Float(_)) => "float_of_json".to_string(),
            TyKind::Adt(tref) => {
                let mut args = tref
                    .generics
                    .types
                    .iter()
                    .map(|ty| self.type_to_ocaml_name(ty))
                    .map(|name| {
                        if !name.chars().all(|c| c.is_alphanumeric()) {
                            format!("({name})")
                        } else {
                            name
                        }
                    })
                    .collect_vec();
                match tref.id {
                    TypeId::Adt(id) => {
                        let mut base_ty = if let Some(tdecl) = self.crate_data.type_decls.get(id) {
                            self.type_to_ocaml_ident(tdecl)
                        } else if let Some(name) = self.crate_data.item_name(id) {
                            eprintln!("Warning: type {} missing from llbc", repr_name(name));
                            name.name
                                .last()
                                .unwrap()
                                .as_ident()
                                .unwrap()
                                .0
                                .to_lowercase()
                        } else {
                            format!("missing_type_{id}")
                        };
                        if base_ty == "vec" {
                            base_ty = "list".to_string();
                        }
                        if base_ty == "ustr" {
                            base_ty = "string".to_string();
                        }
                        if base_ty == "indexed_map" || base_ty == "index_vec" {
                            base_ty = "list".to_string();
                            args.remove(0); // Remove the index generic param
                        }
                        if base_ty == "index_map" {
                            // That's the `indexmap::IndexMap` case. Translate as a list of pairs.
                            base_ty = "list".to_string();
                            args = vec![format!("( {} * {} )", args[0], args[1])]
                        }
                        let args = match args.as_slice() {
                            [] => String::new(),
                            [arg] => arg.clone(),
                            args => format!("({})", args.iter().join(",")),
                        };
                        format!("{args} {base_ty}")
                    }
                    TypeId::Builtin(BuiltinTy::Box) => args[0].clone(),
                    TypeId::Tuple => args.iter().join("*"),
                    _ => unimplemented!("{ty:?}"),
                }
            }
            TyKind::TypeVar(DeBruijnVar::Free(id) | DeBruijnVar::Bound(_, id)) => format!("'a{id}"),
            _ => unimplemented!("{ty:?}"),
        }
    }

    pub fn names_to_type_id_map(&self, data: &[(&str, &str)]) -> HashMap<TypeDeclId, String> {
        data.iter()
            .map(|(name, def)| (self.id_from_name(name), def.to_string()))
            .collect()
    }

    pub fn names_to_type_id_set(&self, data: &[&str]) -> HashSet<TypeDeclId> {
        data.iter().map(|name| self.id_from_name(name)).collect()
    }
}
