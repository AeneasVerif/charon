use crate::ast::*;
use crate::formatter::{AstFormatter, FmtCtx};
use crate::pretty::FmtWithCtx;
use derive_generic_visitor::*;
use macros::EnumIsA;
use std::fmt::{self, Debug};

/// Each `GenericArgs` is meant for a corresponding `GenericParams`; this describes which one.
#[derive(Debug, Clone, Eq, PartialEq, Hash, EnumIsA, Drive, DriveMut)]
pub enum GenericsSource {
    /// A top-level item.
    Item(ItemId),
    /// A trait method.
    Method(TraitDeclId, TraitMethodId),
    /// A trait associated type.
    TraitType(TraitDeclId, AssocTypeId),
    /// A builtin item like `Box`.
    Builtin,
    /// Some other use of generics outside the main Charon ast.
    Other,
}

impl GenericsSource {
    pub fn item<I: Into<ItemId>>(id: I) -> Self {
        Self::Item(id.into())
    }

    /// Return a path that represents the target item.
    pub fn item_name(&self, translated: &TranslatedCrate, fmt_ctx: &FmtCtx) -> String {
        match self {
            GenericsSource::Item(id) => translated.item_name(*id).to_string_with_ctx(fmt_ctx),
            GenericsSource::Method(trait_id, method_name) => format!(
                "{}::{method_name}",
                translated.item_name(*trait_id).to_string_with_ctx(fmt_ctx),
            ),
            GenericsSource::TraitType(trait_id, type_id) => {
                let type_name =
                    fmt::from_fn(|f| fmt_ctx.format_assoc_type_name(f, *trait_id, *type_id));
                format!(
                    "{}::{type_name}",
                    translated.item_name(*trait_id).to_string_with_ctx(fmt_ctx),
                )
            }
            GenericsSource::Builtin => "<built-in>".to_string(),
            GenericsSource::Other => "<unknown>".to_string(),
        }
    }
}

impl TypeId {
    pub fn generics_target(&self) -> GenericsSource {
        match *self {
            TypeId::Adt(decl_id) => GenericsSource::item(decl_id),
            TypeId::Tuple | TypeId::Builtin(..) => GenericsSource::Builtin,
        }
    }
}
impl FunId {
    pub fn generics_target(&self) -> GenericsSource {
        match *self {
            FunId::Regular(fun_id) => GenericsSource::item(fun_id),
            FunId::Builtin(..) => GenericsSource::Builtin,
        }
    }
}
impl FnPtrKind {
    pub fn generics_target(&self) -> GenericsSource {
        match self {
            FnPtrKind::Fun(fun_id) => fun_id.generics_target(),
            FnPtrKind::Trait(trait_ref, name) => {
                GenericsSource::Method(trait_ref.trait_decl_ref.skip_binder.id, *name)
            }
        }
    }
}
