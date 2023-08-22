//! Implementations for [crate::gast]
#![allow(dead_code)]

use crate::expressions::*;
use crate::formatter::Formatter;
use crate::gast::*;
use crate::names::Name;
use crate::types::*;
use crate::values::*;
use serde::Serialize;
use std::cmp::max;
use std::fmt::Debug;

/// Iterate on the declarations' non-empty bodies with their corresponding name and type.
/// TODO: generalize this with visitors
pub fn iter_function_bodies<T: Debug + Clone + Serialize>(
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
pub fn iter_global_bodies<T: Debug + Clone + Serialize>(
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

pub fn fmt_args_raw<'a, 'b, T, R>(
    ctx: &'b T,
    region_args: &'a Vec<R>,
    type_args: &'a Vec<Ty<R>>,
    const_generic_args: &'a Vec<ConstGeneric>,
    mut traits: Vec<String>,
) -> String
where
    T: Formatter<TypeVarId::Id>
        + Formatter<&'a R>
        + Formatter<TypeDeclId::Id>
        + Formatter<ConstGenericVarId::Id>
        + Formatter<FunDeclId::Id>
        + Formatter<GlobalDeclId::Id>
        + Formatter<TraitId::Id>
        + Formatter<TraitClauseId::Id>,
{
    let regions_s: Vec<String> = region_args.iter().map(|x| ctx.format_object(x)).collect();
    let mut types_s: Vec<String> = type_args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    let mut cgs_s: Vec<String> = const_generic_args
        .iter()
        .map(|x| x.fmt_with_ctx(ctx))
        .collect();
    let mut args_s = regions_s;
    args_s.append(&mut types_s);
    args_s.append(&mut cgs_s);
    args_s.append(&mut traits);

    if args_s.is_empty() {
        "".to_string()
    } else {
        format!("<{}>", args_s.join(", "))
    }
}

pub fn fmt_args_no_traits<'a, 'b, T, R>(
    ctx: &'b T,
    region_args: &'a Vec<R>,
    type_args: &'a Vec<Ty<R>>,
    const_generic_args: &'a Vec<ConstGeneric>,
) -> String
where
    T: Formatter<TypeVarId::Id>
        + Formatter<&'a R>
        + Formatter<TypeDeclId::Id>
        + Formatter<ConstGenericVarId::Id>
        + Formatter<FunDeclId::Id>
        + Formatter<GlobalDeclId::Id>
        + Formatter<TraitId::Id>
        + Formatter<TraitClauseId::Id>,
{
    fmt_args_raw(ctx, region_args, type_args, const_generic_args, Vec::new())
}

pub fn fmt_args<'a, 'b, T, R>(
    ctx: &'b T,
    region_args: &'a Vec<R>,
    type_args: &'a Vec<Ty<R>>,
    const_generic_args: &'a Vec<ConstGeneric>,
    traits: &'a Vec<TraitRef>,
) -> String
where
    T: Formatter<TypeVarId::Id>
        + Formatter<&'a R>
        + Formatter<&'a ErasedRegion>
        + Formatter<TypeDeclId::Id>
        + Formatter<ConstGenericVarId::Id>
        + Formatter<FunDeclId::Id>
        + Formatter<GlobalDeclId::Id>
        + Formatter<TraitId::Id>
        + Formatter<TraitClauseId::Id>,
{
    let traits_s: Vec<String> = traits.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    fmt_args_raw(ctx, region_args, type_args, const_generic_args, traits_s)
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
            + Formatter<TraitId::Id>
            + Formatter<TraitClauseId::Id>,
    {
        let def_id = ctx.format_object(self.def_id);
        let params = crate::types::TypeDecl::fmt_params(
            &self.region_params,
            &self.type_params,
            &self.const_generic_params,
        );
        let trait_clauses: Vec<String> = self
            .trait_clauses
            .iter()
            .map(|clause| format!("{TAB_INCR}{}", clause.fmt_with_ctx(ctx)))
            .collect();
        let trait_clauses = if !trait_clauses.is_empty() {
            format!("\nwhere\n{}", trait_clauses.join(",\n"))
        } else {
            "".to_string()
        };
        format!("trait {def_id}{params}{trait_clauses}")
    }
}

impl TraitClause {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: Formatter<TypeVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<TraitId::Id>
            + Formatter<TraitClauseId::Id>,
    {
        let clause_id = ctx.format_object(self.clause_id);
        let trait_id = ctx.format_object(self.trait_id);
        let args = fmt_args_no_traits(
            ctx,
            &self.region_params,
            &self.type_params,
            &self.const_generic_params,
        );
        format!("[{clause_id}]: {trait_id}{args}")
    }
}

impl TraitRef {
    pub fn fmt_with_ctx<'a, C>(&'a self, ctx: &C) -> String
    where
        C: Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<TraitId::Id>
            + Formatter<TraitClauseId::Id>,
    {
        let trait_id = match &self.trait_id {
            TraitOrClauseId::Trait(id) => ctx.format_object(*id),
            TraitOrClauseId::Clause(id) => ctx.format_object(*id),
        };
        let args = fmt_args(
            ctx,
            &self.region_args,
            &self.type_args,
            &self.const_generic_args,
            &self.traits,
        );
        format!("{trait_id}{args}")
    }
}

pub fn fmt_call<'a, 'b, T>(
    ctx: &'b T,
    func: &'a FunIdOrTraitMethodRef,
    region_args: &'a Vec<ErasedRegion>,
    type_args: &'a Vec<ETy>,
    const_generic_args: &'a Vec<ConstGeneric>,
    traits: &'a Vec<TraitRef>,
    args: &'a [Operand],
) -> String
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
        + Formatter<TraitId::Id>
        + Formatter<TraitClauseId::Id>,
{
    let rt_args = fmt_args(ctx, region_args, type_args, const_generic_args, traits);

    let args: Vec<String> = args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    let args = args.join(", ");

    let f = match func {
        FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id)) => {
            format!("{}{}", ctx.format_object(*def_id), rt_args)
        }
        FunIdOrTraitMethodRef::Fun(FunId::Assumed(assumed)) => {
            format!("@{}{rt_args}", assumed.variant_name())
        }
        FunIdOrTraitMethodRef::Trait(trait_ref, method_id) => {
            format!(
                "{}::{}{}",
                trait_ref.fmt_with_ctx(ctx),
                &method_id.0,
                rt_args
            )
        }
    };

    format!("{f}({args})")
}

impl<T: Debug + Clone + Serialize> GExprBody<T> {
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
            + Formatter<&'a T>,
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
            + Formatter<ConstGenericVarId::Id>,
    {
        // Type parameters
        let params = {
            let regions: Vec<String> = self.region_params.iter().map(|x| x.to_string()).collect();
            let mut types: Vec<String> = self.type_params.iter().map(|x| x.to_string()).collect();
            let mut cgs: Vec<String> = self
                .const_generic_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut params = regions;
            params.append(&mut types);
            params.append(&mut cgs);
            if params.is_empty() {
                "".to_string()
            } else {
                format!("<{}>", params.join(", "))
            }
        };

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

        // Regions hierarchy
        let regions_hierarchy: Vec<String> = self
            .regions_hierarchy
            .iter()
            .map(|rg| rg.fmt_with_ctx(ctx))
            .collect();
        let regions_hierarchy = regions_hierarchy.join("\n");

        // Put everything together
        format!("fn{params}({args}){ret_ty}\n\nRegions hierarchy:\n{regions_hierarchy}",)
    }
}

// TODO: there is no point in having a FunSigFormatter anymore - merge with the other
// formatters
pub struct FunSigFormatter<'a, FD, GD, TD> {
    pub ty_ctx: &'a TypeDecls,
    pub fun_ctx: &'a FD,
    pub global_ctx: &'a GD,
    pub trait_ctx: &'a TD,
    pub sig: &'a FunSig,
}

impl<'a, FD, GD, TD> Formatter<TypeVarId::Id> for FunSigFormatter<'a, FD, GD, TD> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.sig.type_params.get(id).unwrap().to_string()
    }
}

impl<'a, FD, GD, TD> Formatter<RegionVarId::Id> for FunSigFormatter<'a, FD, GD, TD> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        self.sig.region_params.get(id).unwrap().to_string()
    }
}

impl<'a, FD, GD, TD> Formatter<&Region<RegionVarId::Id>> for FunSigFormatter<'a, FD, GD, TD> {
    fn format_object(&self, r: &Region<RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'a, FD, GD, TD> Formatter<TypeDeclId::Id> for FunSigFormatter<'a, FD, GD, TD> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.ty_ctx.format_object(id)
    }
}

impl<'a, FD, GD, TD> Formatter<GlobalDeclId::Id> for FunSigFormatter<'a, FD, GD, TD>
where
    GD: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.global_ctx.format_object(id)
    }
}

impl<'a, FD, GD, TD> Formatter<FunDeclId::Id> for FunSigFormatter<'a, FD, GD, TD>
where
    FD: Formatter<FunDeclId::Id>,
{
    fn format_object(&self, id: FunDeclId::Id) -> String {
        self.fun_ctx.format_object(id)
    }
}

impl<'a, FD, GD, TD> Formatter<TraitId::Id> for FunSigFormatter<'a, FD, GD, TD>
where
    TD: Formatter<TraitId::Id>,
{
    fn format_object(&self, id: TraitId::Id) -> String {
        self.trait_ctx.format_object(id)
    }
}

impl<'a, FD, GD, TD> Formatter<TraitClauseId::Id> for FunSigFormatter<'a, FD, GD, TD> {
    fn format_object(&self, id: TraitClauseId::Id) -> String {
        id.to_pretty_string()
    }
}

impl<'a, FD, GD, TD> Formatter<ConstGenericVarId::Id> for FunSigFormatter<'a, FD, GD, TD> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        match self.sig.const_generic_params.get(id) {
            Option::None => {
                error!("Could not find a ConsGenericVarId::Id for pretty-printing");
                id.to_pretty_string()
            }
            Option::Some(cg_var) => cg_var.to_string(),
        }
    }
}

impl FunSig {
    pub fn fmt_with_decls<
        FD: Formatter<FunDeclId::Id>,
        GD: Formatter<GlobalDeclId::Id>,
        TD: Formatter<TraitId::Id>,
    >(
        &self,
        ty_ctx: &TypeDecls,
        fun_ctx: &FD,
        global_ctx: &GD,
        trait_ctx: &TD,
    ) -> String {
        // Initialize the formatting context
        let ctx = FunSigFormatter {
            ty_ctx,
            fun_ctx,
            global_ctx,
            trait_ctx,
            sig: self,
        };

        // Use the context for printing
        self.fmt_with_ctx(&ctx)
    }
}

impl<T: Debug + Clone + Serialize> GFunDecl<T> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// definition). See [`fmt_with_decls`](crate::ullbc_ast::FunDecl::fmt_with_decls).
    pub fn gfmt_with_ctx<'a, 'b, 'c, T1, T2>(
        &'a self,
        tab: &'b str,
        sig_ctx: &'c T1,
        body_ctx: &'c T2,
    ) -> String
    where
        T1: Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<TraitId::Id>
            + Formatter<TraitClauseId::Id>
            + Formatter<FunDeclId::Id>,
        T2: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<&'a T>
            + Formatter<TraitId::Id>
            + Formatter<TraitClauseId::Id>,
    {
        // Function name
        let name = self.name.to_string();

        // Type parameters
        let params = {
            let regions: Vec<String> = self
                .signature
                .region_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut types: Vec<String> = self
                .signature
                .type_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut cgs: Vec<String> = self
                .signature
                .const_generic_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut params = regions;
            params.append(&mut types);
            params.append(&mut cgs);
            if params.is_empty() {
                "".to_string()
            } else {
                format!("<{}>", params.join(", "))
            }
        };

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for i in 0..self.signature.inputs.len() {
            // The input variables start at index 1
            let id = VarId::Id::new(i + 1);
            let arg_ty = &self.signature.inputs.get(i).unwrap();
            args.push(
                format!(
                    "{}: {}",
                    id.to_pretty_string(),
                    arg_ty.fmt_with_ctx(sig_ctx)
                )
                .to_string(),
            );
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.signature.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_string()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(sig_ctx))
        };

        // Where clauses
        let trait_clauses: Vec<String> = self
            .signature
            .trait_clauses
            .iter()
            .map(|clause| format!("{tab}{TAB_INCR}{}", clause.fmt_with_ctx(sig_ctx)))
            .collect();
        let trait_clauses = if !trait_clauses.is_empty() {
            format!("\n{tab}where\n{}\n{tab}", trait_clauses.join(",\n"))
        } else {
            " ".to_string()
        };

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{tab}fn {name}{params}({args}){ret_ty}{trait_clauses}")
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{tab}{TAB_INCR}");
                let body = body.fmt_with_ctx(&body_tab, body_ctx);

                // Put everything together
                format!("{tab}fn {name}{params}({args}){ret_ty}{trait_clauses}{{\n{body}\n{tab}}}",)
            }
        }
    }
}

impl<CD: Debug + Clone + Serialize> GGlobalDecl<CD> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the global definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the global
    /// definition). See [`fmt_with_decls`](crate::ullbc_ast::FunDecl::fmt_with_decls).
    pub fn gfmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, body_ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<&'a CD>,
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
                let body = body.fmt_with_ctx(&body_tab, body_ctx);

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

pub struct GAstFormatter<'ctx, FD, GD, TD> {
    pub type_context: &'ctx TypeDecls,
    pub fun_context: &'ctx FD,
    pub global_context: &'ctx GD,
    pub trait_context: &'ctx TD,
    /// We may not have the list of type variables at hand (if we directly
    /// pretty print a body, for instance). If this is the case, the
    /// formatter will print the variable indices.
    pub type_vars: Option<&'ctx TypeVarId::Vector<TypeVar>>,
    /// Same as for `type_vars`.
    pub vars: Option<&'ctx VarId::Vector<Var>>,
    /// Same as for `type_vars`
    pub const_generic_vars: Option<&'ctx ConstGenericVarId::Vector<ConstGenericVar>>,
    /// Same as for `type_vars`
    pub trait_clauses: Option<&'ctx TraitClauseId::Vector<TraitClause>>,
}

pub struct CtxNames<'ctx> {
    pub type_context: &'ctx TypeDecls,
    pub fun_context: &'ctx FunDeclId::Map<String>,
    pub global_context: &'ctx GlobalDeclId::Map<String>,
    pub trait_context: &'ctx TraitId::Map<String>,
}

impl<'ctx> CtxNames<'ctx> {
    pub fn new(
        type_context: &'ctx TypeDecls,
        fun_context: &'ctx FunDeclId::Map<String>,
        global_context: &'ctx GlobalDeclId::Map<String>,
        trait_context: &'ctx TraitId::Map<String>,
    ) -> Self {
        CtxNames {
            type_context,
            fun_context,
            global_context,
            trait_context,
        }
    }
}

impl<'ctx, FD, GD, TD> GAstFormatter<'ctx, FD, GD, TD> {
    pub fn new(
        type_context: &'ctx TypeDecls,
        fun_context: &'ctx FD,
        global_context: &'ctx GD,
        trait_context: &'ctx TD,
        type_vars: Option<&'ctx TypeVarId::Vector<TypeVar>>,
        vars: Option<&'ctx VarId::Vector<Var>>,
        const_generic_vars: Option<&'ctx ConstGenericVarId::Vector<ConstGenericVar>>,
        trait_clauses: Option<&'ctx TraitClauseId::Vector<TraitClause>>,
    ) -> Self {
        GAstFormatter {
            type_context,
            fun_context,
            global_context,
            trait_context,
            type_vars,
            vars,
            const_generic_vars,
            trait_clauses,
        }
    }
}

impl<'ctx, FD, GD, TD> Formatter<VarId::Id> for GAstFormatter<'ctx, FD, GD, TD> {
    fn format_object(&self, id: VarId::Id) -> String {
        if self.vars.is_some() {
            let v = self.vars.unwrap().get(id).unwrap();
            v.to_string()
        } else {
            id.to_pretty_string()
        }
    }
}

impl<'ctx, FD, GD, TD> Formatter<TypeVarId::Id> for GAstFormatter<'ctx, FD, GD, TD> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        if self.type_vars.is_some() {
            self.type_vars.unwrap().get(id).unwrap().to_string()
        } else {
            id.to_pretty_string()
        }
    }
}

impl<'ctx, FD, GD, TD> Formatter<TraitClauseId::Id> for GAstFormatter<'ctx, FD, GD, TD> {
    fn format_object(&self, id: TraitClauseId::Id) -> String {
        id.to_pretty_string()
    }
}

/// For adt types
impl<'ctx, FD, GD, TD> Formatter<TypeDeclId::Id> for GAstFormatter<'ctx, FD, GD, TD> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.type_context.format_object(id)
    }
}

/// For enum values: `List::Cons`
impl<'ctx, FD, GD, TD> Formatter<(TypeDeclId::Id, VariantId::Id)>
    for GAstFormatter<'ctx, FD, GD, TD>
{
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        let (def_id, variant_id) = id;
        let ctx = self.type_context;
        // The definition may not be available yet, especially if we print-debug
        // while translating the crate
        match ctx.get(def_id) {
            Option::None => format!(
                "{}::{}",
                def_id.to_pretty_string(),
                variant_id.to_pretty_string()
            ),
            Option::Some(def) => {
                let variants = def.kind.as_enum();
                let mut name = def.name.to_string();
                let variant_name = &variants.get(variant_id).unwrap().name;
                name.push_str("::");
                name.push_str(variant_name);
                name
            }
        }
    }
}

/// For struct/enum values: retrieve a field name
impl<'ctx, FD, GD, TD> Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    for GAstFormatter<'ctx, FD, GD, TD>
{
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        let ctx = self.type_context;
        // The definition may not be available yet, especially if we print-debug
        // while translating the crate
        match ctx.get(def_id) {
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

impl<'ctx, FD, GD, TD> Formatter<ConstGenericVarId::Id> for GAstFormatter<'ctx, FD, GD, TD> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        if self.const_generic_vars.is_some() {
            match self.const_generic_vars.unwrap().get(id) {
                Option::None => {
                    error!("Could not find a ConsGenericVarId::Id for pretty-printing");
                    id.to_pretty_string()
                }
                Option::Some(cg_var) => cg_var.to_string(),
            }
        } else {
            id.to_pretty_string()
        }
    }
}

impl<'ctx, FD, GD, TD> Formatter<&ErasedRegion> for GAstFormatter<'ctx, FD, GD, TD> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_string()
    }
}

impl<'ctx, FD, GD, TD> Formatter<&ETy> for GAstFormatter<'ctx, FD, GD, TD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, ty: &ETy) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD, TD> Formatter<&Place> for GAstFormatter<'ctx, FD, GD, TD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, p: &Place) -> String {
        p.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD, TD> Formatter<&Operand> for GAstFormatter<'ctx, FD, GD, TD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, op: &Operand) -> String {
        op.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD, TD> Formatter<&Rvalue> for GAstFormatter<'ctx, FD, GD, TD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, v: &Rvalue) -> String {
        v.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD, TD> Formatter<FunDeclId::Id> for GAstFormatter<'ctx, FD, GD, TD>
where
    FD: Formatter<FunDeclId::Id>,
{
    fn format_object(&self, id: FunDeclId::Id) -> String {
        self.fun_context.format_object(id)
    }
}

impl<'ctx, FD, GD, TD> Formatter<TraitId::Id> for GAstFormatter<'ctx, FD, GD, TD>
where
    TD: Formatter<TraitId::Id>,
{
    fn format_object(&self, id: TraitId::Id) -> String {
        self.trait_context.format_object(id)
    }
}

impl<'ctx, FD, GD, TD> Formatter<GlobalDeclId::Id> for GAstFormatter<'ctx, FD, GD, TD>
where
    GD: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.global_context.format_object(id)
    }
}

pub(crate) struct FunNamesFormatter<'ctx> {
    decls: &'ctx FunDeclId::Map<String>,
}

pub(crate) struct GlobalNamesFormatter<'ctx> {
    decls: &'ctx GlobalDeclId::Map<String>,
}

pub(crate) struct TraitNamesFormatter<'ctx> {
    decls: &'ctx TraitId::Map<String>,
}

impl<'ctx> FunNamesFormatter<'ctx> {
    pub fn new(decls: &'ctx FunDeclId::Map<String>) -> Self {
        FunNamesFormatter { decls }
    }
}

impl<'ctx> Formatter<FunDeclId::Id> for FunNamesFormatter<'ctx> {
    fn format_object(&self, id: FunDeclId::Id) -> String {
        self.decls.get(id).unwrap().clone()
    }
}

impl<'ctx> GlobalNamesFormatter<'ctx> {
    pub fn new(decls: &'ctx GlobalDeclId::Map<String>) -> Self {
        GlobalNamesFormatter { decls }
    }
}

impl<'ctx> Formatter<GlobalDeclId::Id> for GlobalNamesFormatter<'ctx> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.decls.get(id).unwrap().clone()
    }
}

impl<'ctx> TraitNamesFormatter<'ctx> {
    pub fn new(decls: &'ctx TraitId::Map<String>) -> Self {
        TraitNamesFormatter { decls }
    }
}

impl<'ctx> Formatter<TraitId::Id> for TraitNamesFormatter<'ctx> {
    fn format_object(&self, id: TraitId::Id) -> String {
        self.decls.get(id).unwrap().clone()
    }
}

impl FunIdOrTraitMethodRef {
    pub(crate) fn mk_assumed(aid: AssumedFunId) -> Self {
        Self::Fun(FunId::Assumed(aid))
    }
}

impl Formatter<TraitId::Id> for TraitId::Map<TraitDecl> {
    fn format_object(&self, id: TraitId::Id) -> String {
        self.get(id).unwrap().name.to_string()
    }
}
