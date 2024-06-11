use crate::common::TAB_INCR;
use crate::gast;
use crate::ids::Vector;
use crate::llbc_ast;
use crate::llbc_ast::*;
use crate::pretty::{fmt_with_ctx, FmtWithCtx};
use crate::translate_ctx::TranslatedCrate;
use crate::types::*;
use crate::ullbc_ast;
use crate::ullbc_ast as ast;
use crate::values::*;

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
        let FmtCtx {
            translated,
            region_vars: _,
            type_vars: _,
            const_generic_vars: _,
            locals,
        } = self;

        let translated = translated.as_deref();
        let locals = locals.as_deref();
        FmtCtx {
            translated,
            region_vars: im::vector![generics.regions.clone()],
            type_vars: Some(&generics.types),
            const_generic_vars: Some(&generics.const_generics),
            locals,
        }
    }
}

/// We use this trait with the formatter to update the context,
/// for instance when we enter a declaration that we need to print.
pub trait SetLocals<'a> {
    type C: 'a + AstFormatter;

    fn set_locals(&'a self, locals: &'a Vector<VarId, ast::Var>) -> Self::C;
}

impl<'a, 'b> SetLocals<'a> for FmtCtx<'b> {
    type C = FmtCtx<'a>;

    fn set_locals(&'a self, locals: &'a Vector<VarId, ast::Var>) -> Self::C {
        let FmtCtx {
            translated,
            region_vars,
            type_vars,
            const_generic_vars,
            locals: _,
        } = self;

        let translated = translated.as_deref();
        let type_vars = type_vars.as_deref();
        let const_generic_vars = const_generic_vars.as_deref();
        FmtCtx {
            translated,
            region_vars: region_vars.clone(),
            type_vars,
            const_generic_vars,
            locals: Some(locals),
        }
    }
}

/// We use this trait to update the context by pushing a group of bound regions.
pub trait PushBoundRegions<'a> {
    type C: 'a + AstFormatter;

    fn push_bound_regions(&'a self, regions: &Vector<RegionId, RegionVar>) -> Self::C;
}

impl<'a, 'b> PushBoundRegions<'a> for FmtCtx<'b> {
    type C = FmtCtx<'a>;

    fn push_bound_regions(&'a self, regions: &Vector<RegionId, RegionVar>) -> Self::C {
        let FmtCtx {
            translated,
            region_vars,
            type_vars,
            const_generic_vars,
            locals,
        } = self;

        let translated = translated.as_deref();
        let type_vars = type_vars.as_deref();
        let const_generic_vars = const_generic_vars.as_deref();
        let locals = locals.as_deref();
        let mut region_vars = region_vars.clone();
        region_vars.push_front(regions.clone());
        FmtCtx {
            translated,
            region_vars,
            type_vars,
            const_generic_vars,
            locals,
        }
    }
}

pub trait AstFormatter = Formatter<TypeVarId>
    + Formatter<TypeDeclId>
    + Formatter<ConstGenericVarId>
    + Formatter<FunDeclId>
    + Formatter<GlobalDeclId>
    + Formatter<BodyId>
    + Formatter<TraitDeclId>
    + Formatter<TraitImplId>
    + Formatter<TraitClauseId>
    + Formatter<(DeBruijnId, RegionId)>
    + Formatter<VarId>
    + Formatter<(TypeDeclId, VariantId)>
    + Formatter<(TypeDeclId, Option<VariantId>, FieldId)>
    + for<'a> Formatter<&'a Vector<ullbc_ast::BlockId, ullbc_ast::BlockData>>
    + for<'a> Formatter<&'a llbc_ast::Statement>
    + for<'a> SetGenerics<'a>
    + for<'a> SetLocals<'a>
    + for<'a> PushBoundRegions<'a>;

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
pub struct FmtCtx<'a> {
    pub translated: Option<&'a TranslatedCrate>,
    /// The region variables are not an option, because we need to be able to push/pop
    pub region_vars: im::Vector<Vector<RegionId, RegionVar>>,
    pub type_vars: Option<&'a Vector<TypeVarId, TypeVar>>,
    pub const_generic_vars: Option<&'a Vector<ConstGenericVarId, ConstGenericVar>>,
    pub locals: Option<&'a Vector<VarId, ast::Var>>,
}

impl<'a> FmtCtx<'a> {
    pub fn new() -> Self {
        FmtCtx {
            translated: None,
            region_vars: im::Vector::new(),
            type_vars: None,
            const_generic_vars: None,
            locals: None,
        }
    }
}

impl<'a> Default for FmtCtx<'a> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Formatter<TypeDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: TypeDeclId) -> String {
        match &self.translated {
            None => id.to_pretty_string(),
            Some(translated) => match translated.type_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<GlobalDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: GlobalDeclId) -> String {
        match &self.translated {
            None => id.to_pretty_string(),
            Some(translated) => match translated.global_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<ast::FunDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: ast::FunDeclId) -> String {
        match &self.translated {
            None => id.to_pretty_string(),
            Some(translated) => match translated.fun_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<BodyId> for FmtCtx<'a> {
    fn format_object(&self, id: BodyId) -> String {
        match &self.translated {
            None => "<error>".to_owned(),
            Some(translated) => match translated.bodies.get(id) {
                None => "<error>".to_owned(),
                Some(d) => d.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<ast::TraitDeclId> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitDeclId) -> String {
        match &self.translated {
            None => id.to_pretty_string(),
            Some(translated) => match translated.trait_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<ast::TraitImplId> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitImplId) -> String {
        match &self.translated {
            None => id.to_pretty_string(),
            Some(translated) => match translated.trait_impls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<(DeBruijnId, RegionId)> for FmtCtx<'a> {
    fn format_object(&self, (grid, id): (DeBruijnId, RegionId)) -> String {
        match self.region_vars.get(grid.index) {
            None => bound_region_var_to_pretty_string(grid, id),
            Some(gr) => match gr.get(id) {
                None => bound_region_var_to_pretty_string(grid, id),
                Some(v) => v.to_string(),
            },
        }
    }
}

impl<'a> Formatter<TypeVarId> for FmtCtx<'a> {
    fn format_object(&self, id: TypeVarId) -> String {
        match &self.type_vars {
            None => id.to_pretty_string(),
            Some(vars) => match vars.get(id) {
                None => id.to_pretty_string(),
                Some(v) => v.to_string(),
            },
        }
    }
}

impl<'a> Formatter<ConstGenericVarId> for FmtCtx<'a> {
    fn format_object(&self, id: ConstGenericVarId) -> String {
        match &self.const_generic_vars {
            None => id.to_pretty_string(),
            Some(vars) => match vars.get(id) {
                None => id.to_pretty_string(),
                Some(v) => v.to_string(),
            },
        }
    }
}

impl<'a> Formatter<ast::TraitClauseId> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitClauseId) -> String {
        id.to_pretty_string()
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
                    Option::None => format!(
                        "{}::{}",
                        def_id.to_pretty_string(),
                        variant_id.to_pretty_string()
                    ),
                    Option::Some(def) => {
                        let variants = def.kind.as_enum();
                        let mut name = def.name.fmt_with_ctx(self);
                        let variant_name = &variants.get(variant_id).unwrap().name;
                        name.push_str("::");
                        name.push_str(variant_name);
                        name
                    }
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
                Option::None => format!(
                    "{}::{}",
                    def_id.to_pretty_string(),
                    field_id.to_pretty_string()
                ),
                Option::Some(variant_id) => format!(
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
                    Option::None => match opt_variant_id {
                        Option::None => format!(
                            "{}::{}",
                            def_id.to_pretty_string(),
                            field_id.to_pretty_string()
                        ),
                        Option::Some(variant_id) => format!(
                            "{}::{}::{}",
                            def_id.to_pretty_string(),
                            variant_id.to_pretty_string(),
                            field_id.to_pretty_string()
                        ),
                    },
                    Option::Some(gen_def) => match (&gen_def.kind, opt_variant_id) {
                        (TypeDeclKind::Enum(variants), Some(variant_id)) => {
                            let field = variants
                                .get(variant_id)
                                .unwrap()
                                .fields
                                .get(field_id)
                                .unwrap();
                            match &field.name {
                                Option::Some(name) => name.clone(),
                                Option::None => field_id.to_string(),
                            }
                        }
                        (TypeDeclKind::Struct(fields), None) => {
                            let field = fields.get(field_id).unwrap();
                            match &field.name {
                                Option::Some(name) => name.clone(),
                                Option::None => field_id.to_string(),
                            }
                        }
                        _ => unreachable!(),
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
            Some(vars) => match vars.get(id) {
                None => id.to_pretty_string(),
                Some(v) => v.to_string(),
            },
        }
    }
}

impl<'a> Formatter<&llbc_ast::Statement> for FmtCtx<'a> {
    fn format_object(&self, x: &llbc_ast::Statement) -> String {
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
        match &self.translated {
            None => format!("Unknown decl: {:?}", id),
            Some(translated) => match translated.type_decls.get(id) {
                None => {
                    format!("Unknown decl: {:?}", id)
                }
                Some(d) => d.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> DeclFormatter<GlobalDeclId> for FmtCtx<'a> {
    fn format_decl(&self, id: GlobalDeclId) -> String {
        match &self.translated {
            None => format!("Unknown decl: {:?}", id),
            Some(translated) => match translated.global_decls.get(id) {
                None => {
                    format!("Unknown decl: {:?}", id)
                }
                Some(d) => d.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> DeclFormatter<FunDeclId> for FmtCtx<'a> {
    fn format_decl(&self, id: FunDeclId) -> String {
        match &self.translated {
            None => format!("Unknown decl: {:?}", id),
            Some(translated) => match translated.fun_decls.get(id) {
                None => {
                    format!("Unknown decl: {:?}", id)
                }
                Some(d) => d.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> DeclFormatter<TraitDeclId> for FmtCtx<'a> {
    fn format_decl(&self, id: TraitDeclId) -> String {
        match &self.translated {
            None => format!("Unknown decl: {:?}", id),
            Some(translated) => match translated.trait_decls.get(id) {
                None => {
                    format!("Unknown decl: {:?}", id)
                }
                Some(d) => d.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> DeclFormatter<TraitImplId> for FmtCtx<'a> {
    fn format_decl(&self, id: TraitImplId) -> String {
        match &self.translated {
            None => format!("Unknown impl: {:?}", id),
            Some(translated) => match translated.trait_impls.get(id) {
                None => {
                    format!("Unknown impl: {:?}", id)
                }
                Some(d) => d.fmt_with_ctx(self),
            },
        }
    }
}
