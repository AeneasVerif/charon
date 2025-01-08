use std::borrow::Cow;
use std::collections::VecDeque;

use crate::ast::*;
use crate::common::TAB_INCR;
use crate::gast;
use crate::ids::Vector;
use crate::llbc_ast;
use crate::pretty::{fmt_with_ctx, FmtWithCtx};
use crate::ullbc_ast;
use crate::ullbc_ast as ast;

/// [`Formatter`](Formatter) is a trait for converting objects to string.
///
/// We need it because pretty-printing data structures often requires some
/// context. For instance, because values use value ids to point to other values,
/// we need a context to give us the mapping from value ids to values when pretty
/// printing. As the `EvalContext` data structure handles such a mapping, we
/// implement the `Formatter<ValueId>` trait for it.
///
/// Our way of implementing pretty-printing for data-structures while factorizing
/// the code is as follows:
/// - for every data structure which requires formatting, we implement a
///   function `fn fmt_with_ctx(&self, ctx: T) -> String`, with proper trait
///   constraints on the context type T. We implement this kind of functions
///   for values, types, places, operands, rvalues, statements, etc, and
///   the formatting trait constraints often require the context to implement
///   `Formatter` for a various set of indices (type variable index, variable
///   index, type definition index, etc.).
/// - later on, whenever we have a suitable context type (like `EvalContext`),
///   we implement the `Formatter` trait for all the index types we need, and
///   then can easily implement it for all the above data-structures (values,
///   types, places, etc.) by calling the appropriate `fmt_with_ctx` functions.
/// The advantage of using auxiliary `fmt_with_ctx` functions is that we can
/// easily reuse those functions to implement pretty-printing with different
/// contexts, without duplicating the "non-trivial" code.
pub trait Formatter<T> {
    fn format_object(&self, x: T) -> String;
}

/// Provided some id, print the declaration (not simply its name).
pub trait DeclFormatter<Id> {
    fn format_decl(&self, x: Id) -> String;
}

impl<C, T> Formatter<T> for &C
where
    C: Formatter<T>,
{
    fn format_object(&self, x: T) -> String {
        (*self).format_object(x)
    }
}

pub trait IntoFormatter {
    type C: AstFormatter;

    fn into_fmt(self) -> Self::C;
}

impl<C: AstFormatter> IntoFormatter for C {
    type C = Self;

    fn into_fmt(self) -> Self::C {
        self
    }
}

/// We use this trait with the formatter to update the context,
/// for instance when we enter a declaration that we need to print.
pub trait SetGenerics<'a> {
    type C: 'a + AstFormatter;

    fn set_generics(&'a self, generics: &'a GenericParams) -> Self::C;
}

impl<'a, 'b> SetGenerics<'a> for FmtCtx<'b> {
    type C = FmtCtx<'a>;

    fn set_generics(&'a self, generics: &'a GenericParams) -> Self::C {
        FmtCtx {
            translated: self.translated.as_deref(),
            generics: [Cow::Borrowed(generics)].into(),
            locals: self.locals.as_deref(),
        }
    }
}

/// We use this trait with the formatter to update the context,
/// for instance when we enter a declaration that we need to print.
pub trait SetLocals<'a> {
    type C: 'a + AstFormatter;

    fn set_locals(&'a self, locals: &'a Locals) -> Self::C;
}

impl<'a, 'b> SetLocals<'a> for FmtCtx<'b> {
    type C = FmtCtx<'a>;

    fn set_locals(&'a self, locals: &'a Locals) -> Self::C {
        FmtCtx {
            translated: self.translated.as_deref(),
            generics: self.generics.clone(),
            locals: Some(locals),
        }
    }
}

/// We use this trait to update the context by pushing a group of bound regions.
pub trait PushBinder<'a> {
    type C: 'a + AstFormatter;

    fn push_binder(&'a self, new_params: Cow<'a, GenericParams>) -> Self::C;

    fn push_bound_regions(&'a self, regions: &'a Vector<RegionId, RegionVar>) -> Self::C {
        self.push_binder(Cow::Owned(GenericParams {
            regions: regions.clone(),
            ..Default::default()
        }))
    }
}

impl<'a, 'b> PushBinder<'a> for FmtCtx<'b> {
    type C = FmtCtx<'a>;

    fn push_binder(&'a self, new_params: Cow<'a, GenericParams>) -> Self::C {
        let mut generics = self.generics.clone();
        generics.push_front(new_params);
        FmtCtx {
            translated: self.translated.as_deref(),
            generics,
            locals: self.locals.as_deref(),
        }
    }
}

pub trait AstFormatter = Formatter<TypeDeclId>
    + Formatter<FunDeclId>
    + Formatter<GlobalDeclId>
    + Formatter<TraitDeclId>
    + Formatter<TraitImplId>
    + Formatter<AnyTransId>
    + Formatter<RegionDbVar>
    + Formatter<TypeDbVar>
    + Formatter<ConstGenericDbVar>
    + Formatter<ClauseDbVar>
    + Formatter<VarId>
    + Formatter<(TypeDeclId, VariantId)>
    + Formatter<(TypeDeclId, Option<VariantId>, FieldId)>
    + for<'a> Formatter<&'a ImplElem>
    + for<'a> Formatter<&'a RegionVar>
    + for<'a> Formatter<&'a Vector<ullbc_ast::BlockId, ullbc_ast::BlockData>>
    + for<'a> Formatter<&'a llbc_ast::Block>
    + for<'a> SetGenerics<'a>
    + for<'a> SetLocals<'a>
    + for<'a> PushBinder<'a>;

/// For formatting.
///
/// Note that we use the ULLBC definitions, even when formatting LLBC
/// definitions. It doesn't really matter, as all we use is the *name*
/// of the definitions.
///
/// Remark: we take shared borrows to the top-level declarations, but
/// clone the generics, because we may dive into different contexts and may
/// need to update those. We can think of a smarter way of doing this, but
/// for now it is simple and efficient enough.
#[derive(Default)]
pub struct FmtCtx<'a> {
    pub translated: Option<&'a TranslatedCrate>,
    /// Generics form a stack, where each binder introduces a new level. For DeBruijn indices to
    /// work, we keep the innermost parameters at the start of the vector.
    pub generics: VecDeque<Cow<'a, GenericParams>>,
    pub locals: Option<&'a Locals>,
}

impl<'a> FmtCtx<'a> {
    pub fn new() -> Self {
        FmtCtx::default()
    }

    pub fn format_decl_id(&self, id: AnyTransId) -> String {
        match id {
            AnyTransId::Type(id) => self.format_decl(id),
            AnyTransId::Fun(id) => self.format_decl(id),
            AnyTransId::Global(id) => self.format_decl(id),
            AnyTransId::TraitDecl(id) => self.format_decl(id),
            AnyTransId::TraitImpl(id) => self.format_decl(id),
        }
    }

    pub fn get_item(&self, id: AnyTransId) -> Result<AnyTransItem<'_>, Option<&Name>> {
        let Some(translated) = &self.translated else {
            return Err(None);
        };
        translated
            .get_item(id)
            .ok_or_else(|| translated.item_name(id))
    }

    fn format_any_decl(&self, id: AnyTransId) -> String {
        match self.get_item(id) {
            Ok(d) => d.fmt_with_ctx(self),
            Err(opt_name) => {
                let opt_name = opt_name
                    .map(|n| n.fmt_with_ctx(self))
                    .map(|n| format!(" ({n})"))
                    .unwrap_or_default();
                format!("Missing decl: {id:?}{opt_name}")
            }
        }
    }
}

impl<'a> Formatter<TypeDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: TypeDeclId) -> String {
        self.format_object(AnyTransId::from(id))
    }
}

impl<'a> Formatter<GlobalDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: GlobalDeclId) -> String {
        self.format_object(AnyTransId::from(id))
    }
}

impl<'a> Formatter<FunDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: ast::FunDeclId) -> String {
        self.format_object(AnyTransId::from(id))
    }
}

impl<'a> Formatter<TraitDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitDeclId) -> String {
        self.format_object(AnyTransId::from(id))
    }
}

impl<'a> Formatter<TraitImplId> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitImplId) -> String {
        self.format_object(AnyTransId::from(id))
    }
}

impl<'a> Formatter<AnyTransId> for FmtCtx<'a> {
    fn format_object(&self, id: AnyTransId) -> String {
        match self
            .translated
            .and_then(|translated| translated.item_name(id))
        {
            None => id.to_string(),
            Some(name) => name.fmt_with_ctx(self),
        }
    }
}

impl<'a> Formatter<RegionDbVar> for FmtCtx<'a> {
    fn format_object(&self, var: RegionDbVar) -> String {
        if self.generics.is_empty() {
            return format!("'_{var}");
        }
        let (dbid, varid) = match var {
            DeBruijnVar::Bound(dbid, varid) => (dbid.index, varid),
            DeBruijnVar::Free(varid) => (self.generics.len() - 1, varid),
        };
        match self
            .generics
            .get(dbid)
            .and_then(|generics| generics.regions.get(varid))
        {
            None => format!("wrong_region('_{var})"),
            Some(v) => match &v.name {
                Some(name) => name.to_string(),
                None if dbid == self.generics.len() - 1 => format!("'_{varid}"),
                None => format!("'_{var}"),
            },
        }
    }
}

impl<'a> Formatter<&RegionVar> for FmtCtx<'a> {
    fn format_object(&self, var: &RegionVar) -> String {
        match &var.name {
            Some(name) => name.to_string(),
            None => format!("'_{}", var.index),
        }
    }
}

impl<'a> Formatter<TypeDbVar> for FmtCtx<'a> {
    fn format_object(&self, var: TypeDbVar) -> String {
        if self.generics.is_empty() {
            return format!("@Type{var}");
        }
        let (dbid, varid) = match var {
            DeBruijnVar::Bound(dbid, varid) => (dbid.index, varid),
            DeBruijnVar::Free(varid) => (self.generics.len() - 1, varid),
        };
        match self
            .generics
            .get(dbid)
            .and_then(|generics| generics.types.get(varid))
        {
            None => format!("missing_type_var({var})"),
            Some(v) => v.to_string(),
        }
    }
}

impl<'a> Formatter<ConstGenericDbVar> for FmtCtx<'a> {
    fn format_object(&self, var: ConstGenericDbVar) -> String {
        if self.generics.is_empty() {
            return format!("@ConstGeneric{var}");
        }
        let (dbid, varid) = match var {
            DeBruijnVar::Bound(dbid, varid) => (dbid.index, varid),
            DeBruijnVar::Free(varid) => (self.generics.len() - 1, varid),
        };
        match self
            .generics
            .get(dbid)
            .and_then(|generics| generics.const_generics.get(varid))
        {
            None => format!("missing_cg_var({var})"),
            Some(v) => v.to_string(),
        }
    }
}

impl<'a> Formatter<ClauseDbVar> for FmtCtx<'a> {
    fn format_object(&self, var: ClauseDbVar) -> String {
        if self.generics.is_empty() {
            return format!("@TraitClause{var}");
        }
        let (dbid, varid) = match var {
            DeBruijnVar::Bound(dbid, varid) => (dbid.index, varid),
            DeBruijnVar::Free(varid) => (self.generics.len() - 1, varid),
        };
        match self
            .generics
            .get(dbid)
            .and_then(|generics| generics.trait_clauses.get(varid))
        {
            None => format!("missing_clause_var({var})"),
            Some(_) if dbid == self.generics.len() - 1 => format!("@TraitClause{varid}"),
            Some(_) => format!("@TraitClause{var}"),
        }
    }
}

impl<'a> Formatter<&ImplElem> for FmtCtx<'a> {
    fn format_object(&self, elem: &ImplElem) -> String {
        let inner = match elem {
            ImplElem::Ty(bound_ty) => {
                // Just printing the generics (not the predicates)
                let ctx = self.set_generics(&bound_ty.params);
                bound_ty.skip_binder.fmt_with_ctx(&ctx)
            }
            ImplElem::Trait(impl_id) => {
                match &self.translated {
                    None => format!("impl#{impl_id}"),
                    Some(translated) => match translated.trait_impls.get(*impl_id) {
                        None => format!("impl#{impl_id}"),
                        Some(timpl) => {
                            // We need to put the first type parameter aside: it is
                            // the type for which we implement the trait.
                            // This is not very clean because it's hard to move the
                            // first element out of a vector...
                            let ctx = &self.set_generics(&timpl.generics);
                            let TraitDeclRef { trait_id, generics } = &timpl.impl_trait;
                            let (ty, generics) = generics.pop_first_type_arg();
                            let tr = TraitDeclRef {
                                trait_id: *trait_id,
                                generics,
                            };
                            format!("impl {} for {}", tr.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
                        }
                    },
                }
            }
        };

        format!("{{{inner}}}")
    }
}

/// For enum values: `List::Cons`
impl<'a> Formatter<(TypeDeclId, VariantId)> for FmtCtx<'a> {
    fn format_object(&self, id: (TypeDeclId, VariantId)) -> String {
        let (def_id, variant_id) = id;
        match &self.translated {
            None => format!(
                "{}::{}",
                def_id.to_pretty_string(),
                variant_id.to_pretty_string()
            ),
            Some(translated) => {
                // The definition may not be available yet, especially if we print-debug
                // while translating the crate
                match translated.type_decls.get(def_id) {
                    None => format!(
                        "{}::{}",
                        def_id.to_pretty_string(),
                        variant_id.to_pretty_string()
                    ),
                    Some(def) if def.kind.is_enum() => {
                        let variants = def.kind.as_enum().unwrap();
                        let mut name = def.item_meta.name.fmt_with_ctx(self);
                        let variant_name = &variants.get(variant_id).unwrap().name;
                        name.push_str("::");
                        name.push_str(variant_name);
                        name
                    }
                    _ => format!("__unknown_variant"),
                }
            }
        }
    }
}

/// For struct/enum values: retrieve a field name
impl<'a> Formatter<(TypeDeclId, Option<VariantId>, FieldId)> for FmtCtx<'a> {
    fn format_object(&self, id: (TypeDeclId, Option<VariantId>, FieldId)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        match &self.translated {
            None => match opt_variant_id {
                None => format!(
                    "{}::{}",
                    def_id.to_pretty_string(),
                    field_id.to_pretty_string()
                ),
                Some(variant_id) => format!(
                    "{}::{}::{}",
                    def_id.to_pretty_string(),
                    variant_id.to_pretty_string(),
                    field_id.to_pretty_string()
                ),
            },
            Some(translated) =>
            // The definition may not be available yet, especially if we
            // print-debug while translating the crate
            {
                match translated.type_decls.get(def_id) {
                    None => match opt_variant_id {
                        None => format!(
                            "{}::{}",
                            def_id.to_pretty_string(),
                            field_id.to_pretty_string()
                        ),
                        Some(variant_id) => format!(
                            "{}::{}::{}",
                            def_id.to_pretty_string(),
                            variant_id.to_pretty_string(),
                            field_id.to_pretty_string()
                        ),
                    },
                    Some(gen_def) => match (&gen_def.kind, opt_variant_id) {
                        (TypeDeclKind::Enum(variants), Some(variant_id)) => {
                            let field = variants
                                .get(variant_id)
                                .unwrap()
                                .fields
                                .get(field_id)
                                .unwrap();
                            match &field.name {
                                Some(name) => name.clone(),
                                None => field_id.to_string(),
                            }
                        }
                        (TypeDeclKind::Struct(fields) | TypeDeclKind::Union(fields), None) => {
                            let field = fields.get(field_id).unwrap();
                            match &field.name {
                                Some(name) => name.clone(),
                                None => field_id.to_string(),
                            }
                        }
                        _ => format!("__unknown_field"),
                    },
                }
            }
        }
    }
}

impl<'a> Formatter<VarId> for FmtCtx<'a> {
    fn format_object(&self, id: VarId) -> String {
        match &self.locals {
            None => id.to_pretty_string(),
            Some(locals) => match locals.vars.get(id) {
                None => id.to_pretty_string(),
                Some(v) => v.to_string(),
            },
        }
    }
}

impl<'a> Formatter<&llbc_ast::Block> for FmtCtx<'a> {
    fn format_object(&self, x: &llbc_ast::Block) -> String {
        x.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&Vector<ullbc_ast::BlockId, ullbc_ast::BlockData>> for FmtCtx<'a> {
    fn format_object(&self, x: &Vector<ullbc_ast::BlockId, ullbc_ast::BlockData>) -> String {
        fmt_with_ctx::fmt_body_blocks_with_ctx(x, TAB_INCR, self)
    }
}

impl<'a> Formatter<&Ty> for FmtCtx<'a> {
    fn format_object(&self, x: &Ty) -> String {
        x.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&TypeDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &TypeDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&ullbc_ast::ExprBody> for FmtCtx<'a> {
    fn format_object(&self, body: &ullbc_ast::ExprBody) -> String {
        body.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&llbc_ast::ExprBody> for FmtCtx<'a> {
    fn format_object(&self, body: &llbc_ast::ExprBody) -> String {
        body.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&gast::FunDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &llbc_ast::FunDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&gast::GlobalDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &llbc_ast::GlobalDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&FunSig> for FmtCtx<'a> {
    fn format_object(&self, x: &FunSig) -> String {
        x.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&gast::TraitDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &gast::TraitDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&gast::TraitImpl> for FmtCtx<'a> {
    fn format_object(&self, def: &gast::TraitImpl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> DeclFormatter<TypeDeclId> for FmtCtx<'a> {
    fn format_decl(&self, id: TypeDeclId) -> String {
        self.format_any_decl(id.into())
    }
}

impl<'a> DeclFormatter<GlobalDeclId> for FmtCtx<'a> {
    fn format_decl(&self, id: GlobalDeclId) -> String {
        self.format_any_decl(id.into())
    }
}

impl<'a> DeclFormatter<FunDeclId> for FmtCtx<'a> {
    fn format_decl(&self, id: FunDeclId) -> String {
        self.format_any_decl(id.into())
    }
}

impl<'a> DeclFormatter<TraitDeclId> for FmtCtx<'a> {
    fn format_decl(&self, id: TraitDeclId) -> String {
        self.format_any_decl(id.into())
    }
}

impl<'a> DeclFormatter<TraitImplId> for FmtCtx<'a> {
    fn format_decl(&self, id: TraitImplId) -> String {
        self.format_any_decl(id.into())
    }
}
