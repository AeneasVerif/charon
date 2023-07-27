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
    funs: &mut FunDeclId::Vector<GFunDecl<T>>,
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
    globals: &mut GlobalDeclId::Vector<GGlobalDecl<T>>,
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

impl std::string::ToString for Var {
    fn to_string(&self) -> String {
        let id = var_id_to_pretty_string(self.index);
        match &self.name {
            // We display both the variable name and its id because some
            // variables may have the same name (in different scopes)
            Some(name) => format!("{name}({id})"),
            None => id,
        }
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

pub fn fmt_call<'a, 'b, T>(
    ctx: &'b T,
    func: &'a FunId,
    region_args: &'a Vec<ErasedRegion>,
    type_args: &'a Vec<ETy>,
    const_generic_args: &'a Vec<ConstGeneric>,
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
        + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
{
    let rt_args = if region_args.len() + type_args.len() + const_generic_args.len() == 0 {
        "".to_string()
    } else {
        let regions_s: Vec<String> = region_args.iter().map(|x| x.to_string()).collect();
        let mut types_s: Vec<String> = type_args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
        let mut cgs_s: Vec<String> = const_generic_args
            .iter()
            .map(|x| x.fmt_with_ctx(ctx))
            .collect();
        let mut s = regions_s;
        s.append(&mut types_s);
        s.append(&mut cgs_s);
        format!("<{}>", s.join(", "))
    };
    let args: Vec<String> = args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    let args = args.join(", ");

    let f = match func {
        FunId::Regular(def_id) => format!("{}{}", ctx.format_object(*def_id), rt_args),
        FunId::Assumed(assumed) => {
            format!("@{}<{rt_args}>", assumed.variant_name())
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

            let var_name = match &v.name {
                Some(name) => name.clone(),
                None => var_id_to_pretty_string(v.index),
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
            + Formatter<ConstGenericVarId::Id>,
    {
        // Type parameters
        let params = if self.region_params.len() + self.type_params.len() == 0 {
            "".to_string()
        } else {
            let regions: Vec<String> = self.region_params.iter().map(|x| x.to_string()).collect();
            let mut types: Vec<String> = self.type_params.iter().map(|x| x.to_string()).collect();
            let mut params = regions;
            params.append(&mut types);
            format!("<{}>", params.join(", "))
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

pub struct FunSigFormatter<'a> {
    pub ty_ctx: &'a TypeDecls,
    pub sig: &'a FunSig,
}

impl<'a> Formatter<TypeVarId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.sig.type_params.get(id).unwrap().to_string()
    }
}

impl<'a> Formatter<RegionVarId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        self.sig.region_params.get(id).unwrap().to_string()
    }
}

impl<'a> Formatter<&Region<RegionVarId::Id>> for FunSigFormatter<'a> {
    fn format_object(&self, r: &Region<RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<TypeDeclId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.ty_ctx.format_object(id)
    }
}

impl<'a> Formatter<ConstGenericVarId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        let cg_var = self.sig.const_generic_params.get(id).unwrap();
        cg_var.to_string()
    }
}

impl FunSig {
    pub fn fmt_with_decls(&self, ty_ctx: &TypeDecls) -> String {
        // Initialize the formatting context
        let ctx = FunSigFormatter { ty_ctx, sig: self };

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
            + Formatter<ConstGenericVarId::Id>,
        T2: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<ConstGenericVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<&'a T>,
    {
        // Function name
        let name = self.name.to_string();

        // Type parameters
        let params = if self.signature.region_params.len() + self.signature.type_params.len() == 0 {
            "".to_string()
        } else {
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
            let mut params = regions;
            params.append(&mut types);
            format!("<{}>", params.join(", "))
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
                    var_id_to_pretty_string(id),
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

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{tab}fn {name}{params}({args}){ret_ty}")
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{tab}{TAB_INCR}");
                let body = body.fmt_with_ctx(&body_tab, body_ctx);

                // Put everything together
                format!("{tab}fn {name}{params}({args}){ret_ty} {{\n{body}\n{tab}}}",)
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

pub struct GAstFormatter<'ctx, FD, GD> {
    pub type_context: &'ctx TypeDecls,
    pub fun_context: &'ctx FD,
    pub global_context: &'ctx GD,
    /// We may not have the list of type variables at hand (if we directly
    /// pretty print a body, for instance). If this is the case, the
    /// formatter will print the variable indices.
    pub type_vars: Option<&'ctx TypeVarId::Vector<TypeVar>>,
    /// Same as for `type_vars`.
    pub vars: Option<&'ctx VarId::Vector<Var>>,
    /// Same as for `type_vars`
    pub const_generic_vars: Option<&'ctx ConstGenericVarId::Vector<ConstGenericVar>>,
}

pub struct CtxNames<'ctx> {
    pub type_context: &'ctx TypeDecls,
    pub fun_context: &'ctx FunDeclId::Vector<String>,
    pub global_context: &'ctx GlobalDeclId::Vector<String>,
}

impl<'ctx> CtxNames<'ctx> {
    pub fn new(
        type_context: &'ctx TypeDecls,
        fun_context: &'ctx FunDeclId::Vector<String>,
        global_context: &'ctx GlobalDeclId::Vector<String>,
    ) -> Self {
        CtxNames {
            type_context,
            fun_context,
            global_context,
        }
    }
}

impl<'ctx, FD, GD> GAstFormatter<'ctx, FD, GD> {
    pub fn new(
        type_context: &'ctx TypeDecls,
        fun_context: &'ctx FD,
        global_context: &'ctx GD,
        type_vars: Option<&'ctx TypeVarId::Vector<TypeVar>>,
        vars: Option<&'ctx VarId::Vector<Var>>,
        const_generic_vars: Option<&'ctx ConstGenericVarId::Vector<ConstGenericVar>>,
    ) -> Self {
        GAstFormatter {
            type_context,
            fun_context,
            global_context,
            type_vars,
            vars,
            const_generic_vars,
        }
    }
}

impl<'ctx, FD, GD> Formatter<VarId::Id> for GAstFormatter<'ctx, FD, GD> {
    fn format_object(&self, id: VarId::Id) -> String {
        if self.vars.is_some() {
            let v = self.vars.unwrap().get(id).unwrap();
            v.to_string()
        } else {
            var_id_to_pretty_string(id)
        }
    }
}

impl<'ctx, FD, GD> Formatter<TypeVarId::Id> for GAstFormatter<'ctx, FD, GD> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        if self.type_vars.is_some() {
            self.type_vars.unwrap().get(id).unwrap().to_string()
        } else {
            type_var_id_to_pretty_string(id)
        }
    }
}

/// For adt types
impl<'ctx, FD, GD> Formatter<TypeDeclId::Id> for GAstFormatter<'ctx, FD, GD> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.type_context.format_object(id)
    }
}

/// For enum values: `List::Cons`
impl<'ctx, FD, GD> Formatter<(TypeDeclId::Id, VariantId::Id)> for GAstFormatter<'ctx, FD, GD> {
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        let (def_id, variant_id) = id;
        let ctx = self.type_context;
        let def = ctx.get_type_def(def_id).unwrap();
        let variants = def.kind.as_enum();
        let mut name = def.name.to_string();
        let variant_name = &variants.get(variant_id).unwrap().name;
        name.push_str("::");
        name.push_str(variant_name);
        name
    }
}

/// For struct/enum values: retrieve a field name
impl<'ctx, FD, GD> Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    for GAstFormatter<'ctx, FD, GD>
{
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        let ctx = self.type_context;
        let gen_def = ctx.get_type_def(def_id).unwrap();
        match (&gen_def.kind, opt_variant_id) {
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
        }
    }
}

impl<'ctx, FD, GD> Formatter<ConstGenericVarId::Id> for GAstFormatter<'ctx, FD, GD> {
    fn format_object(&self, id: ConstGenericVarId::Id) -> String {
        if self.const_generic_vars.is_some() {
            let v = self.const_generic_vars.unwrap().get(id).unwrap();
            v.to_string()
        } else {
            const_generic_var_id_to_pretty_string(id)
        }
    }
}

impl<'ctx, FD, GD> Formatter<&ErasedRegion> for GAstFormatter<'ctx, FD, GD> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_string()
    }
}

impl<'ctx, FD, GD> Formatter<&ETy> for GAstFormatter<'ctx, FD, GD> {
    fn format_object(&self, ty: &ETy) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD> Formatter<&Place> for GAstFormatter<'ctx, FD, GD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, p: &Place) -> String {
        p.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD> Formatter<&Operand> for GAstFormatter<'ctx, FD, GD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, op: &Operand) -> String {
        op.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD> Formatter<&Rvalue> for GAstFormatter<'ctx, FD, GD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, v: &Rvalue) -> String {
        v.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD> Formatter<FunDeclId::Id> for GAstFormatter<'ctx, FD, GD>
where
    FD: Formatter<FunDeclId::Id>,
{
    fn format_object(&self, id: FunDeclId::Id) -> String {
        self.fun_context.format_object(id)
    }
}

impl<'ctx, FD, GD> Formatter<GlobalDeclId::Id> for GAstFormatter<'ctx, FD, GD>
where
    GD: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.global_context.format_object(id)
    }
}

pub(crate) struct FunNamesFormatter<'ctx> {
    decls: &'ctx FunDeclId::Vector<String>,
}

pub(crate) struct GlobalNamesFormatter<'ctx> {
    decls: &'ctx GlobalDeclId::Vector<String>,
}

impl<'ctx> FunNamesFormatter<'ctx> {
    pub fn new(decls: &'ctx FunDeclId::Vector<String>) -> Self {
        FunNamesFormatter { decls }
    }
}

impl<'ctx> Formatter<FunDeclId::Id> for FunNamesFormatter<'ctx> {
    fn format_object(&self, id: FunDeclId::Id) -> String {
        self.decls.get(id).unwrap().clone()
    }
}

impl<'ctx> GlobalNamesFormatter<'ctx> {
    pub fn new(decls: &'ctx GlobalDeclId::Vector<String>) -> Self {
        GlobalNamesFormatter { decls }
    }
}

impl<'ctx> Formatter<GlobalDeclId::Id> for GlobalNamesFormatter<'ctx> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        self.decls.get(id).unwrap().clone()
    }
}
