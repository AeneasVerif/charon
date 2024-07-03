use crate::formatter::{FmtCtx, Formatter, IntoFormatter};
use crate::gast::*;
use crate::ids::{Generator, Vector};
use crate::meta::{FileId, FileName, LocalFileId, VirtualFileId};
use crate::reorder_decls::DeclarationsGroups;
use crate::types::*;
use derive_visitor::{Drive, DriveMut};
use linked_hash_set::LinkedHashSet;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use rustc_hir::def_id::DefId;
use serde::{Deserialize, Serialize};
use std::cmp::{Ord, PartialOrd};
use std::collections::HashMap;
use std::fmt;

/// The id of a translated item.
#[derive(
    Copy,
    Clone,
    Debug,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
#[charon::rename("AnyDeclId")]
#[charon::variants_prefix("Id")]
pub enum AnyTransId {
    Type(TypeDeclId),
    Fun(FunDeclId),
    Global(GlobalDeclId),
    TraitDecl(TraitDeclId),
    TraitImpl(TraitImplId),
}

/// Implement `TryFrom`  and `From` to convert between an enum and its variants.
macro_rules! wrap_unwrap_enum {
    ($enum:ident::$variant:ident($variant_ty:ident)) => {
        impl TryFrom<$enum> for $variant_ty {
            type Error = ();
            fn try_from(x: $enum) -> Result<Self, Self::Error> {
                match x {
                    $enum::$variant(x) => Ok(x),
                    _ => Err(()),
                }
            }
        }

        impl From<$variant_ty> for $enum {
            fn from(x: $variant_ty) -> Self {
                $enum::$variant(x)
            }
        }
    };
}

wrap_unwrap_enum!(AnyTransId::Fun(FunDeclId));
wrap_unwrap_enum!(AnyTransId::Global(GlobalDeclId));
wrap_unwrap_enum!(AnyTransId::Type(TypeDeclId));
wrap_unwrap_enum!(AnyTransId::TraitDecl(TraitDeclId));
wrap_unwrap_enum!(AnyTransId::TraitImpl(TraitImplId));

/// A translated item.
#[derive(Debug, Clone, Copy, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity)]
pub enum AnyTransItem<'ctx> {
    Type(&'ctx TypeDecl),
    Fun(&'ctx FunDecl),
    Global(&'ctx GlobalDecl),
    TraitDecl(&'ctx TraitDecl),
    TraitImpl(&'ctx TraitImpl),
}

/// The data of a translated crate.
#[derive(Default)]
pub struct TranslatedCrate {
    /// The name of the crate.
    pub crate_name: String,

    /// File names to ids and vice-versa
    pub file_to_id: HashMap<FileName, FileId>,
    pub id_to_file: HashMap<FileId, FileName>,
    pub real_file_counter: Generator<LocalFileId>,
    pub virtual_file_counter: Generator<VirtualFileId>,

    /// All the ids, in the order in which we encountered them
    pub all_ids: LinkedHashSet<AnyTransId>,
    /// The map from rustc id to translated id.
    pub id_map: HashMap<DefId, AnyTransId>,
    /// The reverse map of ids.
    pub reverse_id_map: HashMap<AnyTransId, DefId>,

    /// The translated type definitions
    pub type_decls: Vector<TypeDeclId, TypeDecl>,
    /// The translated function definitions
    pub fun_decls: Vector<FunDeclId, FunDecl>,
    /// The translated global definitions
    pub global_decls: Vector<GlobalDeclId, GlobalDecl>,
    /// The bodies of functions and constants
    pub bodies: Vector<BodyId, Body>,
    /// The translated trait declarations
    pub trait_decls: Vector<TraitDeclId, TraitDecl>,
    /// The translated trait declarations
    pub trait_impls: Vector<TraitImplId, TraitImpl>,
    /// The re-ordered groups of declarations, initialized as empty.
    pub ordered_decls: Option<DeclarationsGroups>,
}

impl TranslatedCrate {
    pub fn get_item(&self, trans_id: AnyTransId) -> Option<AnyTransItem<'_>> {
        match trans_id {
            AnyTransId::Type(id) => self.type_decls.get(id).map(AnyTransItem::Type),
            AnyTransId::Fun(id) => self.fun_decls.get(id).map(AnyTransItem::Fun),
            AnyTransId::Global(id) => self.global_decls.get(id).map(AnyTransItem::Global),
            AnyTransId::TraitDecl(id) => self.trait_decls.get(id).map(AnyTransItem::TraitDecl),
            AnyTransId::TraitImpl(id) => self.trait_impls.get(id).map(AnyTransItem::TraitImpl),
        }
    }
}

impl fmt::Display for TranslatedCrate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let fmt: FmtCtx = self.into_fmt();
        match &self.ordered_decls {
            None => {
                // We do simple: types, globals, traits, functions
                for d in &self.type_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.global_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.trait_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.trait_impls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
                for d in &self.fun_decls {
                    writeln!(f, "{}\n", fmt.format_object(d))?
                }
            }
            Some(ordered_decls) => {
                for gr in ordered_decls {
                    for id in gr.get_ids() {
                        writeln!(f, "{}\n", fmt.format_decl_id(id))?
                    }
                }
            }
        }
        fmt::Result::Ok(())
    }
}

impl<'tcx, 'ctx, 'a> IntoFormatter for &'a TranslatedCrate {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        FmtCtx {
            translated: Some(self),
            ..Default::default()
        }
    }
}
