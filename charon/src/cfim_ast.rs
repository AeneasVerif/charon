//! CFIM: Control-Flow Internal MIR
//!
//! MIR code where we have rebuilt the control-flow (`if ... then ... else ...`,
//! `while ...`, ...).
//!
//! Also note that we completely break the definitions Statement and Terminator
//! from MIR to use Statement and Expression. The Statement definition in this
//! file doesn't correspond at all to the Statement definition from MIR.

#![allow(dead_code)]
use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::im_ast::*;
use crate::types::*;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};

#[derive(Debug, Clone, Serialize)]
pub struct Assert {
    pub cond: Operand,
    pub expected: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct Call {
    pub func: FunId,
    /// Technically this is useless, but we still keep it because we might
    /// want to introduce some information (and the way we encode from MIR
    /// is as simple as possible - and in MIR we also have a vector of erased
    /// regions).
    pub region_params: Vec<ErasedRegion>,
    pub type_params: Vec<ETy>,
    pub args: Vec<Operand>,
    pub dest: Place,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum Statement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId::Id),
    Drop(Place),
    Assert(Assert),
    Call(Call),
    /// Panic also handles "unreachable"
    Panic,
    Return,
    /// Break to outer loops.
    /// The `usize` gives the index of the outer loop to break to:
    /// * 0: break to first outer loop (the current loop)
    /// * 1: break to second outer loop
    /// * ...
    Break(usize),
    /// Continue to outer loops.
    /// The `usize` gives the index of the outer loop to continue to:
    /// * 0: continue to first outer loop (the current loop)
    /// * 1: continue to second outer loop
    /// * ...
    Continue(usize),
    /// No-op.
    Nop,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(Box<Expression>, Box<Expression>),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    /// Also, we use a `LinkedHashMap` to make sure the order of the switch
    /// branches is preserved.
    SwitchInt(
        IntegerTy,
        LinkedHashMap<ScalarValue, Expression>,
        Box<Expression>,
    ),
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum Expression {
    Statement(Statement),
    Sequence(Box<Expression>, Box<Expression>),
    Switch(Operand, SwitchTargets),
    Loop(Box<Expression>),
}

pub type FunDefs = DefId::Vector<FunDef>;

/// A function definition
pub type FunDef = GFunDef<Expression>;

impl SwitchTargets {
    pub fn get_targets(&self) -> Vec<&Expression> {
        match self {
            SwitchTargets::If(exp1, exp2) => {
                vec![exp1, exp2]
            }
            SwitchTargets::SwitchInt(_, targets, otherwise) => {
                let mut out: Vec<&Expression> = vec![otherwise];
                for (_, tgt) in targets {
                    out.push(tgt);
                }
                out
            }
        }
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
            SwitchTargets::If(e1, e2) => {
                vs.serialize_field(e1)?;
                vs.serialize_field(e2)?;
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
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<DefId::Id>
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
            Statement::Drop(place) => format!("drop {}", place.fmt_with_ctx(ctx),).to_owned(),
            Statement::Assert(assert) => format!(
                "assert({} == {})",
                assert.cond.fmt_with_ctx(ctx),
                assert.expected,
            )
            .to_owned(),
            Statement::Call(call) => {
                let Call {
                    func,
                    region_params,
                    type_params,
                    args,
                    dest,
                } = call;
                let params = if region_params.len() + type_params.len() == 0 {
                    "".to_owned()
                } else {
                    let regions_s: Vec<String> =
                        region_params.iter().map(|x| x.to_string()).collect();
                    let mut types_s: Vec<String> =
                        type_params.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
                    let mut s = regions_s;
                    s.append(&mut types_s);
                    format!("<{}>", s.join(", ")).to_owned()
                };
                let args: Vec<String> = args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
                let args = args.join(", ");

                let f = match func {
                    FunId::Local(def_id) => {
                        format!("{}{}", ctx.format_object(*def_id), params).to_owned()
                    }
                    FunId::Assumed(assumed) => match assumed {
                        AssumedFunId::BoxNew => {
                            format!("alloc::boxed::Box{}::new", params).to_owned()
                        }
                        AssumedFunId::BoxDeref => {
                            format!("core::ops::deref::Deref<Box{}>::deref", params).to_owned()
                        }
                        AssumedFunId::BoxDerefMut => {
                            format!("core::ops::deref::DerefMut<Box{}>::deref_mut", params)
                                .to_owned()
                        }
                        AssumedFunId::BoxFree => {
                            format!("alloc::alloc::box_free<{}>", params).to_owned()
                        }
                    },
                };

                format!("{} := {}({})", dest.fmt_with_ctx(ctx), f, args,).to_owned()
            }
            Statement::Panic => "panic".to_owned(),
            Statement::Return => "return".to_owned(),
            Statement::Break(index) => format!("break {}", index).to_owned(),
            Statement::Continue(index) => format!("continue {}", index).to_owned(),
            Statement::Nop => "nop".to_owned(),
        }
    }
}

impl Expression {
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<DefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Expression::Statement(st) => format!("{}{};", tab, st.fmt_with_ctx(ctx)),
            Expression::Sequence(e1, e2) => format!(
                "{}\n{}",
                e1.fmt_with_ctx(tab, ctx),
                e2.fmt_with_ctx(tab, ctx)
            )
            .to_owned(),
            Expression::Switch(discr, targets) => match targets {
                SwitchTargets::If(true_exp, false_exp) => {
                    let inner_tab = format!("{}{}", tab, TAB_INCR);
                    format!(
                        "{}if {} {{\n{}\n{}}}\n{}else {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        true_exp.fmt_with_ctx(&inner_tab, ctx),
                        tab,
                        tab,
                        false_exp.fmt_with_ctx(&inner_tab, ctx),
                        tab,
                    )
                    .to_owned()
                }
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let inner_tab1 = format!("{}{}", tab, TAB_INCR);
                    let inner_tab2 = format!("{}{}", inner_tab1, TAB_INCR);
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(v, e)| {
                            format!(
                                "{}{} => {{\n{}\n{}}}",
                                inner_tab1,
                                v.to_string(),
                                e.fmt_with_ctx(&inner_tab2, ctx),
                                inner_tab1
                            )
                            .to_owned()
                        })
                        .collect();
                    maps.push(
                        format!(
                            "{}_ => {{\n{}\n{}}}",
                            inner_tab1,
                            otherwise.fmt_with_ctx(&inner_tab2, ctx),
                            inner_tab1
                        )
                        .to_owned(),
                    );
                    let maps = maps.join(",\n");

                    format!(
                        "{}switch {} {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        maps,
                        tab
                    )
                    .to_owned()
                }
            },
            Expression::Loop(e) => {
                let inner_tab = format!("{}{}", tab, TAB_INCR);
                format!(
                    "{}loop {{\n{}\n{}}}",
                    tab,
                    e.fmt_with_ctx(&inner_tab, ctx),
                    tab
                )
                .to_owned()
            }
        }
    }
}

impl FunDef {
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
            + Formatter<DefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        // Format the body expression
        let body_exp = self.body.fmt_with_ctx(tab, body_ctx);

        // Format the rest
        self.gfmt_with_ctx("", &body_exp, sig_ctx, body_ctx)
    }
}

type AstFormatter<'ctx> = GAstFormatter<'ctx, FunDefs>;

impl<'ctx> Formatter<DefId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: DefId::Id) -> String {
        let f = self.fun_context.get(id).unwrap();
        f.name.to_string()
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
        self.fmt_with_ctx(TAB_INCR, &fun_sig_ctx, &eval_ctx)
    }
}
