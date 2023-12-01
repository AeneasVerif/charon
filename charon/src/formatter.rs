use crate::common::TAB_INCR;
use crate::gast;
use crate::llbc_ast;
use crate::llbc_ast::*;
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
/// implement the `Formatter<ValueId::Id>` trait for it.
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
    type T: AstFormatter;

    fn into_fmt(self) -> Self::T;
}

pub trait AstFormatter = Formatter<TypeVarId::Id>
    + Formatter<TypeDeclId::Id>
    + Formatter<ConstGenericVarId::Id>
    + Formatter<FunDeclId::Id>
    + Formatter<GlobalDeclId::Id>
    + Formatter<TraitDeclId::Id>
    + Formatter<TraitImplId::Id>
    + Formatter<TraitClauseId::Id>
    + Formatter<(DeBruijnId, RegionId::Id)>
    + Formatter<VarId::Id>
    + Formatter<(TypeDeclId::Id, VariantId::Id)>
    + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    + for<'a> Formatter<&'a ullbc_ast::BlockId::Vector<ullbc_ast::BlockData>>
    + for<'a> Formatter<&'a llbc_ast::Statement>;

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
    pub type_decls: Option<&'a TypeDecls>,
    pub fun_decls: Option<&'a ast::FunDecls>,
    pub global_decls: Option<&'a ast::GlobalDecls>,
    pub trait_decls: Option<&'a ast::TraitDecls>,
    pub trait_impls: Option<&'a ast::TraitImpls>,
    pub region_vars: im::Vector<RegionId::Vector<RegionVar>>,
    pub type_vars: TypeVarId::Vector<TypeVar>,
    pub const_generic_vars: ConstGenericVarId::Vector<ConstGenericVar>,
    pub locals: VarId::Vector<ast::Var>,
}

impl<'a> IntoFormatter for FmtCtx<'a> {
    type T = FmtCtx<'a>;

    fn into_fmt(self) -> Self::T {
        self
    }
}

impl<'a, 'b> IntoFormatter for &'b FmtCtx<'a> {
    type T = &'b FmtCtx<'a>;

    fn into_fmt(self) -> Self::T {
        self
    }
}

impl<'a> FmtCtx<'a> {
    pub fn new() -> Self {
        FmtCtx {
            type_decls: None,
            fun_decls: None,
            global_decls: None,
            trait_decls: None,
            trait_impls: None,
            region_vars: im::Vector::new(),
            type_vars: TypeVarId::Vector::new(),
            const_generic_vars: ConstGenericVarId::Vector::new(),
            locals: VarId::Vector::new(),
        }
    }
}

impl<'a> Formatter<TypeDeclId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        match &self.type_decls {
            None => id.to_pretty_string(),
            Some(type_decls) => match type_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<GlobalDeclId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        match &self.global_decls {
            None => id.to_pretty_string(),
            Some(global_decls) => match global_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<ast::FunDeclId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: ast::FunDeclId::Id) -> String {
        match &self.fun_decls {
            None => id.to_pretty_string(),
            Some(fun_decls) => match fun_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<ast::TraitDeclId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitDeclId::Id) -> String {
        match &self.trait_decls {
            None => id.to_pretty_string(),
            Some(trait_decls) => match trait_decls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<ast::TraitImplId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitImplId::Id) -> String {
        match &self.trait_impls {
            None => id.to_pretty_string(),
            Some(trait_impls) => match trait_impls.get(id) {
                None => id.to_pretty_string(),
                Some(d) => d.name.fmt_with_ctx(self),
            },
        }
    }
}

impl<'a> Formatter<(DeBruijnId, RegionId::Id)> for FmtCtx<'a> {
    fn format_object(&self, (grid, id): (DeBruijnId, RegionId::Id)) -> String {
        match self.region_vars.get(grid.index) {
            None => bound_region_var_to_pretty_string(grid, id),
            Some(gr) => match gr.get(id) {
                None => bound_region_var_to_pretty_string(grid, id),
                Some(v) => v.to_string(),
            },
        }
    }
}

impl<'a> Formatter<TypeVarId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'a> Formatter<ConstGenericVarId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'a> Formatter<ast::TraitClauseId::Id> for FmtCtx<'a> {
    fn format_object(&self, id: ast::TraitClauseId::Id) -> String {
        id.to_pretty_string()
    }
}

/// For enum values: `List::Cons`
impl<'a> Formatter<(TypeDeclId::Id, VariantId::Id)> for FmtCtx<'a> {
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        let (def_id, variant_id) = id;
        match &self.type_decls {
            None => format!(
                "{}::{}",
                def_id.to_pretty_string(),
                variant_id.to_pretty_string()
            ),
            Some(type_decls) => {
                // The definition may not be available yet, especially if we print-debug
                // while translating the crate
                match type_decls.get(def_id) {
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
impl<'a> Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)> for FmtCtx<'a> {
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        match &self.type_decls {
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
            Some(type_decls) =>
            // The definition may not be available yet, especially if we
            // print-debug while translating the crate
            {
                match type_decls.get(def_id) {
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

impl<'a> Formatter<VarId::Id> for FmtCtx<'a> {
    fn format_object(&self, v: VarId::Id) -> String {
        v.to_pretty_string()
    }
}

impl<'a> Formatter<&llbc_ast::Statement> for FmtCtx<'a> {
    fn format_object(&self, x: &llbc_ast::Statement) -> String {
        x.fmt_with_ctx(TAB_INCR, self)
    }
}

impl<'a> Formatter<&ullbc_ast::BlockId::Vector<ullbc_ast::BlockData>> for FmtCtx<'a> {
    fn format_object(&self, x: &ullbc_ast::BlockId::Vector<ullbc_ast::BlockData>) -> String {
        ullbc_ast::fmt_body_blocks_with_ctx(x, TAB_INCR, self)
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

impl<'a> Formatter<&ullbc_ast::GlobalDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &ullbc_ast::GlobalDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&llbc_ast::GlobalDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &llbc_ast::GlobalDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&ullbc_ast::ExprBody> for FmtCtx<'a> {
    fn format_object(&self, body: &ullbc_ast::ExprBody) -> String {
        body.fmt_with_ctx(TAB_INCR, self)
    }
}

impl<'a> Formatter<&llbc_ast::ExprBody> for FmtCtx<'a> {
    fn format_object(&self, body: &llbc_ast::ExprBody) -> String {
        body.fmt_with_ctx(TAB_INCR, self)
    }
}

impl<'a> Formatter<&ullbc_ast::FunDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &ullbc_ast::FunDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<&llbc_ast::FunDecl> for FmtCtx<'a> {
    fn format_object(&self, def: &llbc_ast::FunDecl) -> String {
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
