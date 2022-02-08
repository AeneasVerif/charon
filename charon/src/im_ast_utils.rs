//! Implementations for im_ast.rs
#![allow(dead_code)]

use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::im_ast::*;
use crate::types::*;
use crate::values::*;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::iter::FromIterator;

impl std::string::ToString for Var {
    fn to_string(&self) -> String {
        let id = var_id_to_pretty_string(self.index);
        match &self.name {
            // We display both the variable name and its id because some
            // variables may have the same name (in different scopes)
            Some(name) => format!("{}({})", name, id),
            None => id,
        }
    }
}

impl Var {
    /// Substitute the region parameters and type variables and return
    /// the resulting variable
    pub fn substitute(&self, subst: &ETypeSubst) -> Var {
        Var {
            index: self.index,
            name: self.name.clone(),
            ty: self.ty.substitute_types(subst),
        }
    }
}

impl SwitchTargets {
    pub fn get_targets(&self) -> Vec<BlockId::Id> {
        match self {
            SwitchTargets::If(then_tgt, else_tgt) => {
                vec![*then_tgt, *else_tgt]
            }
            SwitchTargets::SwitchInt(_, targets, otherwise) => {
                let mut all_targets = vec![];
                for (_, target) in targets {
                    all_targets.push(*target);
                }
                all_targets.push(*otherwise);
                all_targets
            }
        }
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
    }
}

impl Serialize for SwitchTargets {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "SwitchTargets";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            SwitchTargets::If(id1, id2) => {
                vs.serialize_field(id1)?;
                vs.serialize_field(id2)?;
            }
            SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                vs.serialize_field(int_ty)?;
                let targets = LinkedHashMapSerializer::new(targets);
                vs.serialize_field(&targets)?;
                vs.serialize_field(otherwise)?;
            }
        }
        vs.end()
    }
}

impl Statement {
    /// Substitute the type variables and return the resulting statement.
    pub fn substitute(&self, subst: &ETypeSubst) -> Statement {
        match self {
            Statement::Assign(place, rvalue) => {
                Statement::Assign(place.substitute(subst), rvalue.substitute(subst))
            }
            Statement::FakeRead(place) => Statement::FakeRead(place.substitute(subst)),
            Statement::SetDiscriminant(place, variant_id) => {
                Statement::SetDiscriminant(place.substitute(subst), *variant_id)
            }
            Statement::StorageDead(var_id) => Statement::StorageDead(*var_id),
        }
    }
}

impl Terminator {
    /// Substitute the type variables and return the resulting terminator
    pub fn substitute(&self, subst: &ETypeSubst) -> Terminator {
        match self {
            Terminator::Goto { target } => Terminator::Goto { target: *target },
            Terminator::Switch { discr, targets } => Terminator::Switch {
                discr: discr.substitute(subst),
                targets: targets.substitute(subst),
            },
            Terminator::Panic => Terminator::Panic,
            Terminator::Return => Terminator::Return,
            Terminator::Unreachable => Terminator::Unreachable,
            Terminator::Drop { place, target } => Terminator::Drop {
                place: place.substitute(subst),
                target: *target,
            },
            Terminator::Call {
                func,
                region_params,
                type_params,
                args,
                dest,
                target,
            } => Terminator::Call {
                func: func.clone(),
                region_params: region_params.clone(),
                type_params: type_params
                    .iter()
                    .map(|ty| ty.substitute_types(subst))
                    .collect(),
                args: Vec::from_iter(args.iter().map(|arg| arg.substitute(subst))),
                dest: dest.substitute(subst),
                target: *target,
            },
            Terminator::Assert {
                cond,
                expected,
                target,
            } => Terminator::Assert {
                cond: cond.substitute(subst),
                expected: *expected,
                target: *target,
            },
        }
    }
}

impl BlockData {
    /// Substitute the type variables and return the resulting `BlockData`
    pub fn substitute(&self, subst: &ETypeSubst) -> BlockData {
        let statements = self
            .statements
            .iter()
            .map(|x| x.substitute(subst))
            .collect();
        let terminator = self.terminator.substitute(subst);
        BlockData {
            statements,
            terminator,
        }
    }
}

impl Statement {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Statement::Assign(place, rvalue) => format!(
                "{} := {}",
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            )
            .to_owned(),
            Statement::FakeRead(place) => {
                format!("@fake_read({})", place.fmt_with_ctx(ctx),).to_owned()
            }
            Statement::SetDiscriminant(place, variant_id) => format!(
                "@discriminant({}) := {}",
                place.fmt_with_ctx(ctx),
                variant_id.to_string()
            )
            .to_owned(),
            Statement::StorageDead(vid) => {
                format!("@storage_dead({})", var_id_to_pretty_string(*vid)).to_owned()
            }
        }
    }
}

impl<'ctx> Formatter<&Statement> for AstFormatter<'ctx> {
    fn format_object(&self, statement: &Statement) -> String {
        statement.fmt_with_ctx(self)
    }
}

pub fn fmt_call<'a, 'b, T>(
    ctx: &'b T,
    func: FunId,
    region_params: &'a Vec<ErasedRegion>,
    type_params: &'a Vec<ETy>,
    args: &'a Vec<Operand>,
) -> String
where
    T: Formatter<VarId::Id>
        + Formatter<TypeVarId::Id>
        + Formatter<&'a ErasedRegion>
        + Formatter<TypeDefId::Id>
        + Formatter<FunDefId::Id>
        + Formatter<(TypeDefId::Id, VariantId::Id)>
        + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
{
    let params = if region_params.len() + type_params.len() == 0 {
        "".to_owned()
    } else {
        let regions_s: Vec<String> = region_params.iter().map(|x| x.to_string()).collect();
        let mut types_s: Vec<String> = type_params.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
        let mut s = regions_s;
        s.append(&mut types_s);
        format!("<{}>", s.join(", ")).to_owned()
    };
    let args: Vec<String> = args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    let args = args.join(", ");

    let f = match func {
        FunId::Local(def_id) => format!("{}{}", ctx.format_object(def_id), params).to_owned(),
        FunId::Assumed(assumed) => match assumed {
            AssumedFunId::Replace => format!("core::mem::replace{}", params).to_owned(),
            AssumedFunId::BoxNew => format!("alloc::boxed::Box{}::new", params).to_owned(),
            AssumedFunId::BoxDeref => format!(
                "core::ops::deref::Deref<alloc::boxed::Box{}>::deref",
                params
            )
            .to_owned(),
            AssumedFunId::BoxDerefMut => format!(
                "core::ops::deref::DerefMut<alloc::boxed::Box{}>::deref_mut",
                params
            )
            .to_owned(),
            AssumedFunId::BoxFree => format!("alloc::alloc::box_free{}", params).to_owned(),
            AssumedFunId::VecNew => format!("alloc::vec::Vec{}::new", params).to_owned(),
            AssumedFunId::VecPush => format!("alloc::vec::Vec{}::push", params).to_owned(),
            AssumedFunId::VecInsert => format!("alloc::vec::Vec{}::insert", params).to_owned(),
            AssumedFunId::VecLen => format!("alloc::vec::Vec{}::len", params).to_owned(),
            AssumedFunId::VecIndex => {
                format!("core::ops::index::Index<alloc::vec::Vec{}>::index", params).to_owned()
            }
            AssumedFunId::VecIndexMut => format!(
                "core::ops::index::IndexMut<alloc::vec::Vec{}>::index_mut",
                params
            )
            .to_owned(),
        },
    };

    format!("{}({})", f, args,).to_owned()
}

impl Terminator {
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDefId::Id>
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Terminator::Goto { target } => format!("goto bb{}", target.to_string()).to_owned(),
            Terminator::Switch { discr, targets } => match targets {
                SwitchTargets::If(true_block, false_block) => format!(
                    "if {} -> bb{} else -> bb{}",
                    discr.fmt_with_ctx(ctx),
                    true_block.to_string(),
                    false_block.to_string()
                )
                .to_owned(),
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(v, bid)| {
                            format!("{}: bb{}", v.to_string(), bid.to_string()).to_owned()
                        })
                        .collect();
                    maps.push(format!("otherwise: bb{}", otherwise.to_string()).to_owned());
                    let maps = maps.join(", ");

                    format!("switch {} -> {}", discr.fmt_with_ctx(ctx), maps).to_owned()
                }
            },
            Terminator::Panic => "panic".to_owned(),
            Terminator::Return => "return".to_owned(),
            Terminator::Unreachable => "unreachable".to_owned(),
            Terminator::Drop { place, target } => format!(
                "drop {} -> bb{}",
                place.fmt_with_ctx(ctx),
                target.to_string()
            )
            .to_owned(),
            Terminator::Call {
                func,
                region_params,
                type_params,
                args,
                dest,
                target,
            } => {
                let call = fmt_call(ctx, *func, region_params, type_params, args);

                format!(
                    "{} := {} -> bb{}",
                    dest.fmt_with_ctx(ctx),
                    call,
                    target.to_string(),
                )
                .to_owned()
            }
            Terminator::Assert {
                cond,
                expected,
                target,
            } => format!(
                "assert({} == {}) -> bb{}",
                cond.fmt_with_ctx(ctx),
                expected,
                target.to_string()
            )
            .to_owned(),
        }
    }
}

impl BlockData {
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDefId::Id>
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        let mut out: Vec<String> = Vec::new();

        // Format the statements
        for statement in &self.statements {
            out.push(format!("{}{};\n", tab, statement.fmt_with_ctx(ctx)).to_owned());
        }

        // Format the terminator
        out.push(format!("{}{};", tab, self.terminator.fmt_with_ctx(ctx)).to_owned());

        // Join the strings
        out.join("")
    }
}

impl<T: std::fmt::Debug + Clone + Serialize> GFunDef<T> {
    pub fn fmt_gbody_with_ctx<'a, 'b, 'c, C>(
        &'a self,
        tab: &'b str,
        body: &'b str,
        ctx: &'c C,
    ) -> String
    where
        C: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDefId::Id>
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        // Format the local variables
        let mut locals: Vec<String> = Vec::new();
        for v in &self.locals {
            use crate::id_vector::ToUsize;
            let index = v.index.to_usize();
            let comment = if index == 0 {
                "// return".to_owned()
            } else {
                if index <= self.arg_count {
                    format!("// arg #{}", index).to_owned()
                } else {
                    match &v.name {
                        Some(_) => "// local".to_owned(),
                        None => "// anonymous local".to_owned(),
                    }
                }
            };

            let var_name = match &v.name {
                Some(name) => name.clone(),
                None => var_id_to_pretty_string(v.index),
            };

            locals.push(
                format!(
                    "{}let {}: {}; {}\n",
                    tab,
                    var_name,
                    v.ty.fmt_with_ctx(ctx),
                    comment
                )
                .to_owned(),
            );
        }

        let mut locals = locals.join("");
        locals.push_str("\n");

        // Put everything together
        let mut out = locals;
        out.push_str(body);
        out
    }
}

impl FunDef {
    pub fn fmt_body_blocks_with_ctx<'a, 'b, 'c, C>(&'a self, tab: &'b str, ctx: &'c C) -> String
    where
        C: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDefId::Id>
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        let block_tab = format!("{}{}", tab, TAB_INCR);
        let mut blocks: Vec<String> = Vec::new();
        for (bid, block) in self.body.iter_indexed_values() {
            use crate::id_vector::ToUsize;
            blocks.push(
                format!(
                    "{}bb{}: {{\n{}\n{}}}\n",
                    tab,
                    bid.to_usize(),
                    block.fmt_with_ctx(&block_tab, ctx),
                    tab
                )
                .to_owned(),
            );
        }
        blocks.join("\n")
    }
}

impl FunSig {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>,
    {
        // Type parameters
        let params = if self.region_params.len() + self.type_params.len() == 0 {
            "".to_owned()
        } else {
            let regions: Vec<String> = self.region_params.iter().map(|x| x.to_string()).collect();
            let mut types: Vec<String> = self.type_params.iter().map(|x| x.to_string()).collect();
            let mut params = regions;
            params.append(&mut types);
            format!("<{}>", params.join(", ")).to_owned()
        };

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for ty in &self.inputs {
            args.push(format!("{}", ty.fmt_with_ctx(ctx)).to_owned());
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_owned()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx)).to_owned()
        };

        // Regions hierarchy
        let regions_hierarchy: Vec<String> = self
            .regions_hierarchy
            .iter()
            .map(|rg| rg.fmt_with_ctx(ctx))
            .collect();
        let regions_hierarchy = regions_hierarchy.join("\n");

        // Put everything together
        format!(
            "fn{}({}){}\n\nRegions hierarchy:\n{}",
            params, args, ret_ty, regions_hierarchy
        )
        .to_owned()
    }
}

pub struct FunSigFormatter<'a> {
    pub ty_ctx: &'a TypeDefs,
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

impl<'a> Formatter<TypeDefId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: TypeDefId::Id) -> String {
        self.ty_ctx.format_object(id)
    }
}

impl FunSig {
    pub fn fmt_with_defs<'ctx>(&self, ty_ctx: &'ctx TypeDefs) -> String {
        // Initialize the formatting context
        let ctx = FunSigFormatter { ty_ctx, sig: self };

        // Use the context for printing
        self.fmt_with_ctx(&ctx)
    }
}

impl<T: std::fmt::Debug + Clone + Serialize> GFunDef<T> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// definition). See [`fmt_with_defs`](FunDef::fmt_with_defs).
    pub fn gfmt_with_ctx<'a, 'b, 'c, T1, T2>(
        &'a self,
        tab: &'b str,
        body_exp: &'b str,
        sig_ctx: &'c T1,
        body_ctx: &'c T2,
    ) -> String
    where
        T1: Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>,
        T2: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        // Function name
        let name = self.name.to_string();

        // Type parameters
        let params = if self.signature.region_params.len() + self.signature.type_params.len() == 0 {
            "".to_owned()
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
            format!("<{}>", params.join(", ")).to_owned()
        };

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for i in 1..self.arg_count {
            let id = VarId::Id::new(i);
            let arg_ty = &self.signature.inputs.get(id).unwrap();
            args.push(
                format!(
                    "{}: {}",
                    var_id_to_pretty_string(id),
                    arg_ty.fmt_with_ctx(sig_ctx)
                )
                .to_owned(),
            );
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.signature.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_owned()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(sig_ctx)).to_owned()
        };

        // Body
        let body_tab = format!("{}{}", tab, TAB_INCR);
        let body = self.fmt_gbody_with_ctx(&body_tab, body_exp, body_ctx);

        // Put everything together
        format!(
            "{}fn {}{}({}){} {{\n{}\n{}}}",
            tab, name, params, args, ret_ty, body, tab
        )
        .to_owned()
    }
}

impl FunDef {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// definition). See [`fmt_with_defs`](FunDef::fmt_with_defs).
    pub fn fmt_with_ctx<'a, 'b, 'c, T1, T2>(
        &'a self,
        tab: &'b str,
        sig_ctx: &'c T1,
        body_ctx: &'c T2,
    ) -> String
    where
        T1: Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>,
        T2: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        // Format the body blocks
        let body_blocks = self.fmt_body_blocks_with_ctx(tab, body_ctx);

        // Format the rest
        self.gfmt_with_ctx("", &body_blocks, sig_ctx, body_ctx)
    }
}

pub struct GAstFormatter<'ctx, T> {
    pub type_context: &'ctx TypeDefs,
    pub fun_context: &'ctx T,
    pub type_vars: &'ctx TypeVarId::Vector<TypeVar>,
    pub vars: &'ctx VarId::Vector<Var>,
}

type AstFormatter<'ctx> = GAstFormatter<'ctx, FunDefs>;

impl<'ctx> Formatter<FunDefId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: FunDefId::Id) -> String {
        let f = self.fun_context.get(id).unwrap();
        f.name.to_string()
    }
}

impl<'ctx> Formatter<&Terminator> for AstFormatter<'ctx> {
    fn format_object(&self, terminator: &Terminator) -> String {
        terminator.fmt_with_ctx(self)
    }
}

impl<'ctx, T> GAstFormatter<'ctx, T> {
    pub fn new(
        type_context: &'ctx TypeDefs,
        fun_context: &'ctx T,
        type_vars: &'ctx TypeVarId::Vector<TypeVar>,
        vars: &'ctx VarId::Vector<Var>,
    ) -> Self {
        GAstFormatter {
            type_context,
            fun_context,
            type_vars,
            vars,
        }
    }
}

impl<'ctx, T> Formatter<VarId::Id> for GAstFormatter<'ctx, T> {
    fn format_object(&self, id: VarId::Id) -> String {
        let v = self.vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'ctx, T> Formatter<TypeVarId::Id> for GAstFormatter<'ctx, T> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.type_vars.get(id).unwrap().to_string()
    }
}

/// For adt types
impl<'ctx, T> Formatter<TypeDefId::Id> for GAstFormatter<'ctx, T> {
    fn format_object(&self, id: TypeDefId::Id) -> String {
        self.type_context.format_object(id)
    }
}

/// For enum values: `List::Cons`
impl<'ctx, T> Formatter<(TypeDefId::Id, VariantId::Id)> for GAstFormatter<'ctx, T> {
    fn format_object(&self, id: (TypeDefId::Id, VariantId::Id)) -> String {
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
impl<'ctx, T> Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>
    for GAstFormatter<'ctx, T>
{
    fn format_object(&self, id: (TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        let ctx = self.type_context;
        let gen_def = ctx.get_type_def(def_id).unwrap();
        match (&gen_def.kind, opt_variant_id) {
            (TypeDefKind::Enum(variants), Some(variant_id)) => {
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
            (TypeDefKind::Struct(fields), None) => {
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

impl<'ctx, T> Formatter<&ErasedRegion> for GAstFormatter<'ctx, T> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'ctx, T> Formatter<&ETy> for GAstFormatter<'ctx, T> {
    fn format_object(&self, ty: &ETy) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'ctx, T> Formatter<&Rvalue> for GAstFormatter<'ctx, T> {
    fn format_object(&self, v: &Rvalue) -> String {
        v.fmt_with_ctx(self)
    }
}

impl<'ctx, T> Formatter<&Place> for GAstFormatter<'ctx, T> {
    fn format_object(&self, p: &Place) -> String {
        p.fmt_with_ctx(self)
    }
}

impl<'ctx, T> Formatter<&Operand> for GAstFormatter<'ctx, T> {
    fn format_object(&self, op: &Operand) -> String {
        op.fmt_with_ctx(self)
    }
}

impl FunDef {
    pub fn fmt_with_defs<'ctx>(&self, ty_ctx: &'ctx TypeDefs, fun_ctx: &'ctx FunDefs) -> String {
        // Initialize the contexts
        let fun_sig_ctx = FunSigFormatter {
            ty_ctx,
            sig: &self.signature,
        };

        let eval_ctx =
            AstFormatter::new(ty_ctx, fun_ctx, &self.signature.type_params, &self.locals);

        // Use the contexts for printing
        self.fmt_with_ctx("", &fun_sig_ctx, &eval_ctx)
    }
}
