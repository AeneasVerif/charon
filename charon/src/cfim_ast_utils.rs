//! Implementations for cfim_ast.rs

#![allow(dead_code)]
use crate::cfim_ast::*;
use crate::common::*;
use crate::formatter::Formatter;
use crate::im_ast::{fmt_call, FunDefId, FunSigFormatter, GAstFormatter, TAB_INCR};
use crate::types::*;
use crate::values::*;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};

impl SwitchTargets {
    pub fn get_targets(&self) -> Vec<&Statement> {
        match self {
            SwitchTargets::If(exp1, exp2) => {
                vec![exp1, exp2]
            }
            SwitchTargets::SwitchInt(_, targets, otherwise) => {
                let mut out: Vec<&Statement> = vec![otherwise];
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
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Statement::Assign(place, rvalue) => format!(
                "{}{} := {}",
                tab,
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            )
            .to_owned(),
            Statement::FakeRead(place) => {
                format!("{}@fake_read({})", tab, place.fmt_with_ctx(ctx),).to_owned()
            }
            Statement::SetDiscriminant(place, variant_id) => format!(
                "{}@discriminant({}) := {}",
                tab,
                place.fmt_with_ctx(ctx),
                variant_id.to_string()
            )
            .to_owned(),
            Statement::Drop(place) => {
                format!("{}drop {}", tab, place.fmt_with_ctx(ctx),).to_owned()
            }
            Statement::Assert(assert) => format!(
                "{}assert({} == {})",
                tab,
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
                let call = fmt_call(ctx, *func, region_params, type_params, args);
                format!("{}{} := {}", tab, dest.fmt_with_ctx(ctx), call).to_owned()
            }
            Statement::Panic => format!("{}panic", tab).to_owned(),
            Statement::Return => format!("{}return", tab).to_owned(),
            Statement::Break(index) => format!("{}break {}", tab, index).to_owned(),
            Statement::Continue(index) => format!("{}continue {}", tab, index).to_owned(),
            Statement::Nop => format!("{}nop", tab).to_owned(),
            Statement::Sequence(st1, st2) => format!(
                "{}\n{}",
                st1.fmt_with_ctx(tab, ctx),
                st2.fmt_with_ctx(tab, ctx)
            )
            .to_owned(),
            Statement::Switch(discr, targets) => match targets {
                SwitchTargets::If(true_st, false_st) => {
                    let inner_tab = format!("{}{}", tab, TAB_INCR);
                    format!(
                        "{}if {} {{\n{}\n{}}}\n{}else {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        true_st.fmt_with_ctx(&inner_tab, ctx),
                        tab,
                        tab,
                        false_st.fmt_with_ctx(&inner_tab, ctx),
                        tab,
                    )
                    .to_owned()
                }
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let inner_tab1 = format!("{}{}", tab, TAB_INCR);
                    let inner_tab2 = format!("{}{}", inner_tab1, TAB_INCR);
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(v, st)| {
                            format!(
                                "{}{} => {{\n{}\n{}}}",
                                inner_tab1,
                                v.to_string(),
                                st.fmt_with_ctx(&inner_tab2, ctx),
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
            Statement::Loop(body) => {
                let inner_tab = format!("{}{}", tab, TAB_INCR);
                format!(
                    "{}loop {{\n{}\n{}}}",
                    tab,
                    body.fmt_with_ctx(&inner_tab, ctx),
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
            + Formatter<FunDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        // Format the body expression
        let body_st = self.body.fmt_with_ctx(tab, body_ctx);

        // Format the rest
        self.gfmt_with_ctx("", &body_st, sig_ctx, body_ctx)
    }
}

type AstFormatter<'ctx> = GAstFormatter<'ctx, FunDefs>;

impl<'ctx> Formatter<FunDefId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: FunDefId::Id) -> String {
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
