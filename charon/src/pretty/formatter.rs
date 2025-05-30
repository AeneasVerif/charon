use std::borrow::Cow;
use std::fmt::Display;

use index_vec::Idx;

use crate::ast::*;
use crate::common::TAB_INCR;
use crate::gast;
use crate::ids::Vector;
use crate::llbc_ast;
use crate::pretty::{fmt_with_ctx, FmtWithCtx};
use crate::ullbc_ast;
use crate::ullbc_ast as ast;

/// [`Formatter`] is a trait for converting objects to string.
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

pub trait AstFormatter:
    Formatter<TypeDeclId>
    + Formatter<FunDeclId>
    + Formatter<GlobalDeclId>
    + Formatter<TraitDeclId>
    + Formatter<TraitImplId>
    + Formatter<AnyTransId>
    + Formatter<RegionDbVar>
    + Formatter<TypeDbVar>
    + Formatter<ConstGenericDbVar>
    + Formatter<ClauseDbVar>
    + Formatter<LocalId>
    + Formatter<(TypeDeclId, VariantId)>
    + Formatter<(TypeDeclId, Option<VariantId>, FieldId)>
    + for<'a> Formatter<&'a ImplElem>
    + for<'a> Formatter<&'a RegionVar>
    + for<'a> Formatter<&'a Vector<ullbc_ast::BlockId, ullbc_ast::BlockData>>
    + for<'a> Formatter<&'a llbc_ast::Block>
{
    type Reborrow<'a>: AstFormatter + 'a
    where
        Self: 'a;

    fn get_crate(&self) -> Option<&TranslatedCrate>;
    fn set_generics<'a>(&'a self, generics: &'a GenericParams) -> Self::Reborrow<'a>;
    fn set_locals<'a>(&'a self, locals: &'a Locals) -> Self::Reborrow<'a>;
    fn push_binder<'a>(&'a self, new_params: Cow<'a, GenericParams>) -> Self::Reborrow<'a>;

    fn push_bound_regions<'a>(
        &'a self,
        regions: &'a Vector<RegionId, RegionVar>,
    ) -> Self::Reborrow<'a> {
        self.push_binder(Cow::Owned(GenericParams {
            regions: regions.clone(),
            ..Default::default()
        }))
    }
}
impl<'c> AstFormatter for FmtCtx<'c> {
    type Reborrow<'a>
        = FmtCtx<'a>
    where
        Self: 'a;

    fn get_crate(&self) -> Option<&TranslatedCrate> {
        self.translated
    }
    fn set_generics<'a>(&'a self, generics: &'a GenericParams) -> Self::Reborrow<'a> {
        FmtCtx {
            translated: self.translated.as_deref(),
            generics: BindingStack::new(Cow::Borrowed(generics)),
            locals: self.locals.as_deref(),
        }
    }
    fn set_locals<'a>(&'a self, locals: &'a Locals) -> Self::Reborrow<'a> {
        FmtCtx {
            translated: self.translated.as_deref(),
            generics: self.generics.clone(),
            locals: Some(locals),
        }
    }
    fn push_binder<'a>(&'a self, new_params: Cow<'a, GenericParams>) -> Self::Reborrow<'a> {
        let mut generics = self.generics.clone();
        generics.push(new_params);
        FmtCtx {
            translated: self.translated.as_deref(),
            generics,
            locals: self.locals.as_deref(),
        }
    }
}

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
    pub generics: BindingStack<Cow<'a, GenericParams>>,
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
            .ok_or_else(|| translated.item_short_name(id))
    }

    /// Print the whole definition.
    fn format_decl(&self, id: impl Into<AnyTransId>) -> String {
        let id = id.into();
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
            .and_then(|translated| translated.item_short_name(id))
        {
            None => id.to_string(),
            Some(name) => name.fmt_with_ctx(self),
        }
    }
}

impl<'a> FmtCtx<'a> {
    fn format_bound_var<Id: Idx + Display, T>(
        &self,
        var: DeBruijnVar<Id>,
        var_prefix: &str,
        f: impl Fn(&T) -> Option<String>,
    ) -> String
    where
        GenericParams: HasVectorOf<Id, Output = T>,
    {
        if self.generics.is_empty() {
            return format!("{var_prefix}{var}");
        }
        match self.generics.get_var::<_, GenericParams>(var) {
            None => format!("missing({var_prefix}{var})"),
            Some(v) => match f(v) {
                Some(name) => name,
                None => {
                    let (dbid, varid) = self.generics.as_bound_var(var);
                    if dbid == self.generics.depth() {
                        format!("{var_prefix}{varid}")
                    } else {
                        format!("{var_prefix}{var}")
                    }
                }
            },
        }
    }
}

impl<'a> Formatter<RegionDbVar> for FmtCtx<'a> {
    fn format_object(&self, var: RegionDbVar) -> String {
        self.format_bound_var(var, "'_", |v| v.name.as_ref().map(|name| name.to_string()))
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
        self.format_bound_var(var, "@Type", |v| Some(v.to_string()))
    }
}

impl<'a> Formatter<ConstGenericDbVar> for FmtCtx<'a> {
    fn format_object(&self, var: ConstGenericDbVar) -> String {
        self.format_bound_var(var, "@ConstGeneric", |v| Some(v.fmt_with_ctx(self)))
    }
}

impl<'a> Formatter<ClauseDbVar> for FmtCtx<'a> {
    fn format_object(&self, var: ClauseDbVar) -> String {
        self.format_bound_var(var, "@TraitClause", |_| None)
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
                                generics: Box::new(generics),
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
        let (type_id, variant_id) = id;
        let name = self.format_object(type_id);
        let variant = match &self.translated {
            None => &variant_id.to_pretty_string(),
            Some(translated) => match translated.type_decls.get(type_id) {
                Some(def) if let Some(variants) = def.kind.as_enum() => {
                    &variants.get(variant_id).unwrap().name
                }
                _ => &variant_id.to_pretty_string(),
            },
        };
        format!("{name}::{variant}",)
    }
}

/// For struct/enum values: retrieve a field name
impl<'a> Formatter<(TypeDeclId, Option<VariantId>, FieldId)> for FmtCtx<'a> {
    fn format_object(&self, id: (TypeDeclId, Option<VariantId>, FieldId)) -> String {
        let (type_id, opt_variant_id, field_id) = id;
        match self
            .translated
            .as_ref()
            .and_then(|tr| tr.type_decls.get(type_id))
        {
            None => field_id.to_string(),
            Some(def) => match (&def.kind, opt_variant_id) {
                (TypeDeclKind::Enum(variants), Some(variant_id)) => variants[variant_id].fields
                    [field_id]
                    .name
                    .clone()
                    .unwrap_or_else(|| field_id.to_string()),
                (TypeDeclKind::Struct(fields) | TypeDeclKind::Union(fields), None) => fields
                    [field_id]
                    .name
                    .clone()
                    .unwrap_or_else(|| field_id.to_string()),
                _ => field_id.to_string(),
            },
        }
    }
}

impl<'a> Formatter<LocalId> for FmtCtx<'a> {
    fn format_object(&self, id: LocalId) -> String {
        match &self.locals {
            None => id.to_pretty_string(),
            Some(locals) => match locals.locals.get(id) {
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
