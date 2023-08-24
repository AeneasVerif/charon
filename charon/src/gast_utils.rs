//! Implementations for [crate::gast]
#![allow(dead_code)]

use crate::common::TAB_INCR;
use crate::formatter::Formatter;
use crate::gast::*;
use crate::names::Name;
use crate::types::*;
use crate::values::*;
use serde::Serialize;
use std::cmp::max;

/// Iterate on the declarations' non-empty bodies with their corresponding name and type.
/// TODO: generalize this with visitors
pub fn iter_function_bodies<T>(
    funs: &mut FunDeclId::Map<GFunDecl<T>>,
) -> impl Iterator<Item = (&Name, &mut GExprBody<T>)> {
    funs.iter_mut().flat_map(|f| match f.body.as_mut() {
        None => None, // Option::map was complaining about borrowing f
        Some(b) => Some((&f.name, b)),
    })
}

/// Iterate on the declarations' non-empty bodies with their corresponding name and type.
/// Same as [iter_function_bodies] (but the `flat_map` lambda cannot be generic).
/// TODO: generalize this with visitors
pub fn iter_global_bodies<T>(
    globals: &mut GlobalDeclId::Map<GGlobalDecl<T>>,
) -> impl Iterator<Item = (&Name, &mut GExprBody<T>)> {
    globals.iter_mut().flat_map(|g| match g.body.as_mut() {
        None => None, // Option::map was complaining about borrowing g
        Some(b) => Some((&g.name, b)),
    })
}

/// Makes a lambda that generates a new variable id, pushes a new variable in
/// the body locals with the given type and returns its id.
pub fn make_locals_generator(locals: &mut VarId::Vector<Var>) -> impl FnMut(ETy) -> VarId::Id + '_ {
    let mut next_id = locals.iter().fold(VarId::ZERO, |id, v| max(id, v.index));
    move |ty| {
        next_id.incr();
        let id = next_id;
        locals.push_back(Var {
            index: id,
            name: None,
            ty,
        });
        id
    }
}

impl FunDeclId::Id {
    pub fn to_pretty_string(&self) -> String {
        format!("@Fun{self}")
    }
}

impl std::string::ToString for Var {
    fn to_string(&self) -> String {
        let id = self.index.to_pretty_string();
        match &self.name {
            // We display both the variable name and its id because some
            // variables may have the same name (in different scopes)
            Some(name) => format!("{name}{id}"),
            None => id,
        }
    }
}

impl VarId::Vector<Var> {
    pub fn fresh_var(&mut self, name: Option<String>, ty: ETy) -> VarId::Id {
        let index = VarId::Id::new(self.len());
        self.push_back(Var { index, name, ty });
        index
    }
}

impl Var {
    /// Substitute the region parameters and type variables and return
    /// the resulting variable
    pub fn substitute(&self, subst: &ETypeSubst, cgsubst: &ConstGenericSubst) -> Var {
        Var {
            index: self.index,
            name: self.name.clone(),
            ty: self.ty.substitute_types(subst, cgsubst),
        }
    }
}

impl FunKind {
    pub(crate) fn is_trait_method(&self) -> bool {
        matches!(self, FunKind::Regular)
    }
}

impl TraitDecl {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: Formatter<TypeVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<TraitDeclId::Id>
            + Formatter<TraitClauseId::Id>
            + Formatter<TraitDeclId::Id>,
    {
        let def_id = ctx.format_object(self.def_id);
        let (generics, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);
        let trait_clauses = fmt_where_clauses("", 0, trait_clauses);
        let items = if self.functions.is_empty() {
            "".to_string()
        } else {
            let functions = self
                .functions
                .iter()
                .map(|(name, f)| format!("{TAB_INCR}{name} -> {}\n", ctx.format_object(*f)))
                .collect::<Vec<String>>()
                .join("");
            format!("\n{{\n{functions}}}")
        };

        match &self.of_trait_id {
            None => format!("trait {def_id}{generics}{trait_clauses}{items}"),
            Some(of_trait_id) => {
                let of_trait_id = ctx.format_object(*of_trait_id);
                format!("impl{generics} {of_trait_id} for {def_id}{generics}{trait_clauses}{items}")
            }
        }
    }
}

pub fn fmt_call<'a, 'b, T>(ctx: &'b T, call: &'a Call) -> String
where
    T: Formatter<VarId::Id>
        + Formatter<TypeVarId::Id>
        + Formatter<&'a ErasedRegion>
        + Formatter<TypeDeclId::Id>
        + Formatter<ConstGenericVarId::Id>
        + Formatter<FunDeclId::Id>
        + Formatter<GlobalDeclId::Id>
        + Formatter<(TypeDeclId::Id, VariantId::Id)>
        + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
        + Formatter<TraitDeclId::Id>
        + Formatter<TraitClauseId::Id>,
{
    let generics = call.generics.fmt_with_ctx_split_trait_refs(ctx);
    let f = match &call.func {
        FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id)) => {
            format!("{}{generics}", ctx.format_object(*def_id),)
        }
        FunIdOrTraitMethodRef::Fun(FunId::Assumed(assumed)) => {
            format!("@{}{generics}", assumed.variant_name())
        }
        FunIdOrTraitMethodRef::Trait(trait_ref, method_id) => {
            format!(
                "{}::{}{}",
                trait_ref.fmt_with_ctx(ctx),
                &method_id.0,
                generics
            )
        }
    };

    let args: Vec<String> = call.args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    let args = args.join(", ");

    format!("{f}({args})")
}

impl<T> GExprBody<T> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// definition). See [`fmt_with_decls`](crate::ullbc_ast::FunDecl::fmt_with_decls).
    pub fn fmt_with_ctx<'a, 'b, 'c, C>(&'a self, tab: &'b str, ctx: &'c C) -> String
    where
        C: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<&'a T>
            + Formatter<TraitDeclId::Id>
            + Formatter<TraitClauseId::Id>,
    {
        // Format the local variables
        let mut locals: Vec<String> = Vec::new();
        for v in &self.locals {
            use crate::id_vector::ToUsize;
            let index = v.index.to_usize();
            let comment = if index == 0 {
                "// return".to_string()
            } else if index <= self.arg_count {
                format!("// arg #{index}").to_string()
            } else {
                match &v.name {
                    Some(_) => "// local".to_string(),
                    None => "// anonymous local".to_string(),
                }
            };

            let var_id = v.index.to_pretty_string();
            let var_name = match &v.name {
                Some(name) => format!("{name}{var_id}"),
                None => var_id,
            };

            locals.push(
                format!(
                    "{tab}let {var_name}: {}; {comment}\n",
                    v.ty.fmt_with_ctx(ctx),
                )
                .to_string(),
            );
        }

        let mut locals = locals.join("");
        locals.push('\n');

        // Format the body blocks - TODO: we don't take the indentation
        // into account, here
        let body = ctx.format_object(&self.body);

        // Put everything together
        let mut out = locals;
        out.push_str(&body);
        out
    }
}

impl FunSig {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<GlobalDeclId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<TraitDeclId::Id>
            + Formatter<TraitClauseId::Id>,
    {
        // Generic parameters
        let (params, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for ty in &self.inputs {
            args.push(ty.fmt_with_ctx(ctx).to_string());
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_string()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx))
        };

        // Trait clauses
        let trait_clauses =
            fmt_where_clauses_with_params_info("", &self.parent_params_info, trait_clauses);

        // Regions hierarchy
        let regions_hierarchy: Vec<String> = self
            .regions_hierarchy
            .iter()
            .map(|rg| rg.fmt_with_ctx(ctx))
            .collect();
        let regions_hierarchy = regions_hierarchy.join("\n");

        // Put everything together
        format!(
            "fn{params}({args}){ret_ty}{trait_clauses}\n\nRegions hierarchy:\n{regions_hierarchy}",
        )
    }
}

pub trait GFunDeclFormatter<'a, Body: 'a> = Formatter<VarId::Id>
    + Formatter<TypeVarId::Id>
    + Formatter<TypeDeclId::Id>
    + Formatter<ConstGenericVarId::Id>
    + Formatter<&'a Region<RegionVarId::Id>>
    + Formatter<&'a ErasedRegion>
    + Formatter<FunDeclId::Id>
    + Formatter<GlobalDeclId::Id>
    + Formatter<(TypeDeclId::Id, VariantId::Id)>
    + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    + Formatter<&'a Body>
    + Formatter<TraitDeclId::Id>
    + Formatter<TraitClauseId::Id>;

impl<T> GFunDecl<T> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// definition). See [`fmt_with_decls`](crate::ullbc_ast::FunDecl::fmt_with_decls).
    pub fn gfmt_with_ctx<'a, 'b, 'c, C>(&'a self, tab: &'b str, ctx: &'c C) -> String
    where
        C: GFunDeclFormatter<'a, T>,
    {
        // Function name
        let name = self.name.to_string();

        // Generic parameters
        let (params, trait_clauses) = self.signature.generics.fmt_with_ctx_with_trait_clauses(ctx);

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for i in 0..self.signature.inputs.len() {
            // The input variables start at index 1
            let id = VarId::Id::new(i + 1);
            let arg_ty = &self.signature.inputs.get(i).unwrap();
            args.push(
                format!("{}: {}", id.to_pretty_string(), arg_ty.fmt_with_ctx(ctx)).to_string(),
            );
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.signature.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_string()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx))
        };

        // Trait clauses
        let trait_clauses = fmt_where_clauses_with_params_info(
            tab,
            &self.signature.parent_params_info,
            trait_clauses,
        );

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{tab}fn {name}{params}({args}){ret_ty}{trait_clauses}")
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{tab}{TAB_INCR}");
                let body = body.fmt_with_ctx(&body_tab, ctx);

                // Put everything together
                format!(
                    "{tab}fn {name}{params}({args}){ret_ty}{trait_clauses}\n{tab}{{\n{body}\n{tab}}}",
                )
            }
        }
    }
}

pub trait GGlobalDeclFormatter<'a, Body: 'a> = Formatter<VarId::Id>
    + Formatter<TypeVarId::Id>
    + Formatter<TypeDeclId::Id>
    + Formatter<&'a ErasedRegion>
    + Formatter<ConstGenericVarId::Id>
    + Formatter<FunDeclId::Id>
    + Formatter<GlobalDeclId::Id>
    + Formatter<(TypeDeclId::Id, VariantId::Id)>
    + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    + Formatter<&'a Body>
    + Formatter<TraitDeclId::Id>
    + Formatter<TraitClauseId::Id>;

impl<T> GGlobalDecl<T> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the global definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the global
    /// definition). See [`fmt_with_decls`](crate::ullbc_ast::FunDecl::fmt_with_decls).
    pub fn gfmt_with_ctx<'a, C>(&'a self, tab: &str, ctx: &C) -> String
    where
        C: GGlobalDeclFormatter<'a, T>,
    {
        // Decl name
        let name = self.name.to_string();

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{tab}global {name}")
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{tab}{TAB_INCR}");
                let body = body.fmt_with_ctx(&body_tab, ctx);

                // Put everything together
                format!("{tab}global {name} {{\n{body}\n{tab}}}")
            }
        }
    }
}

impl<T: std::fmt::Debug + Clone + Serialize> GGlobalDecl<T> {
    fn is_opaque(&self) -> bool {
        self.body.is_none()
    }
}

impl FunIdOrTraitMethodRef {
    pub(crate) fn mk_assumed(aid: AssumedFunId) -> Self {
        Self::Fun(FunId::Assumed(aid))
    }
}

impl std::fmt::Display for TraitMethodName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}
