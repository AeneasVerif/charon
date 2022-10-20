//! Implementations for [crate::llbc_ast]

#![allow(dead_code)]
use std::ops::DerefMut;

use crate::common::*;
use crate::expressions::{Operand, Rvalue};
use crate::formatter::Formatter;
use crate::llbc_ast::{
    Call, ExprBody, FunDecl, FunDecls, GlobalDecl, GlobalDecls, Statement, SwitchTargets,
};
use crate::types::*;
use crate::ullbc_ast::{
    fmt_call, CtxNames, FunDeclId, FunNamesFormatter, FunSigFormatter, GAstFormatter, GlobalDeclId,
    GlobalNamesFormatter, TAB_INCR,
};
use crate::values::*;
use itertools::chain;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use take_mut::take;

/// Goes from e.g. [A, B, C] ; D to (A, (B, (C, D))).
pub fn chain_statements(firsts: Vec<Statement>, last: Statement) -> Statement {
    firsts.into_iter().rev().fold(last, |cont, bind| {
        assert!(!bind.is_sequence());
        Statement::Sequence(Box::new(bind), Box::new(cont))
    })
}

/// Utility function for [new_sequence].
/// Efficiently appends a new statement at the rightmost place of a well-formed sequence.
fn append_rightmost(seq: &mut Statement, r: Box<Statement>) {
    let (_l1, l2) = match seq {
        Statement::Sequence(l1, l2) => (l1, l2),
        _ => unreachable!(),
    };
    if l2.is_sequence() {
        append_rightmost(l2, r);
    } else {
        take(l2.deref_mut(), move |l2| {
            Statement::Sequence(Box::new(l2), r)
        });
    }
}

/// Builds a sequence from well-formed statements.
/// Ensures that the left statement will not be a sequence in the new sequence:
/// Must be used instead of the raw [Statement::Sequence] constructor,
/// unless you're sure that the left statement is not a sequence.
pub fn new_sequence(mut l: Statement, r: Statement) -> Statement {
    let r = Box::new(r);
    match l {
        Statement::Sequence(_, _) => {
            append_rightmost(&mut l, r);
            l
        }
        l => Statement::Sequence(Box::new(l), r),
    }
}

/// Visit an rvalue and generate statements. Used below in [transform_operands].
fn transform_rvalue_operands<F: FnMut(&mut Operand) -> Vec<Statement>>(
    rval: &mut Rvalue,
    f: &mut F,
) -> Vec<Statement> {
    match rval {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => f(op),
        Rvalue::BinaryOp(_, o1, o2) => chain(f(o1), f(o2)).collect(),
        Rvalue::Aggregate(_, ops) => ops.iter_mut().flat_map(f).collect(),
        Rvalue::Discriminant(_) | Rvalue::Ref(_, _) => vec![],
    }
}

/// Transform a statement by visiting its operands and inserting the generated
/// statements before each visited operand.
/// Useful to implement a pass on operands (see e.g., [crate::extract_global_assignments]).
pub fn transform_operands<F: FnMut(&mut Operand) -> Vec<Statement>>(
    st: Statement,
    f: &mut F,
) -> Statement {
    // Does two matchs, depending if we want to move or to borrow the statement.
    let mut st = match st {
        // Recursive calls
        Statement::Loop(s) => Statement::Loop(Box::new(transform_operands(*s, f))),
        Statement::Sequence(s1, s2) => {
            new_sequence(transform_operands(*s1, f), transform_operands(*s2, f))
        }
        Statement::Switch(op, tgt) => Statement::Switch(
            op,
            match tgt {
                SwitchTargets::If(s1, s2) => SwitchTargets::If(
                    Box::new(transform_operands(*s1, f)),
                    Box::new(transform_operands(*s2, f)),
                ),
                SwitchTargets::SwitchInt(ty, vec, s) => SwitchTargets::SwitchInt(
                    ty,
                    vec.into_iter()
                        .map(|(v, s)| (v, transform_operands(s, f)))
                        .collect(),
                    Box::new(transform_operands(*s, f)),
                ),
            },
        ),
        _ => st,
    };
    let new_st = match &mut st {
        // Actual transformations
        Statement::Switch(op, _) => f(op),
        Statement::Assign(_, r) => transform_rvalue_operands(r, f),
        Statement::Call(c) => c.args.iter_mut().flat_map(f).collect(),
        Statement::Assert(a) => f(&mut a.cond),

        // Identity (complete match for compile-time errors when new statements are created)
        Statement::AssignGlobal(_, _)
        | Statement::FakeRead(_)
        | Statement::SetDiscriminant(_, _)
        | Statement::Drop(_)
        | Statement::Panic
        | Statement::Return
        | Statement::Break(_)
        | Statement::Continue(_)
        | Statement::Nop
        | Statement::Sequence(_, _)
        | Statement::Loop(_) => vec![],
    };
    chain_statements(new_st, st)
}

/// Apply a map transformer on statements, in a bottom-up manner.
/// Useful to implement a pass on operands: see e.g. [remove_drop_never].
pub fn transform_statements<F: FnMut(Statement) -> Statement>(
    f: &mut F,
    st: Statement,
) -> Statement {
    // Apply the transformer bottom-up
    let st = match st {
        Statement::Switch(op, tgt) => {
            let tgt = match tgt {
                SwitchTargets::If(mut st1, mut st2) => {
                    *st1 = transform_statements(f, *st1);
                    *st2 = transform_statements(f, *st2);
                    SwitchTargets::If(st1, st2)
                }
                SwitchTargets::SwitchInt(int_ty, branches, mut otherwise) => {
                    let branches: Vec<(Vec<ScalarValue>, Statement)> = branches
                        .into_iter()
                        .map(|x| (x.0, transform_statements(f, x.1)))
                        .collect();
                    *otherwise = transform_statements(f, *otherwise);
                    SwitchTargets::SwitchInt(int_ty, branches, otherwise)
                }
            };
            Statement::Switch(op, tgt)
        }
        Statement::Assign(p, r) => Statement::Assign(p, r),
        Statement::Call(c) => Statement::Call(c),
        Statement::Assert(a) => Statement::Assert(a),
        Statement::AssignGlobal(vid, g) => Statement::AssignGlobal(vid, g),
        Statement::FakeRead(p) => Statement::FakeRead(p),
        Statement::SetDiscriminant(p, vid) => Statement::SetDiscriminant(p, vid),
        Statement::Drop(p) => Statement::Drop(p),
        Statement::Panic => Statement::Panic,
        Statement::Return => Statement::Return,
        Statement::Break(i) => Statement::Break(i),
        Statement::Continue(i) => Statement::Continue(i),
        Statement::Nop => Statement::Nop,
        Statement::Sequence(st1, st2) => {
            let st1 = transform_statements(f, *st1);
            let st2 = transform_statements(f, *st2);
            new_sequence(st1, st2)
        }
        Statement::Loop(mut st) => {
            *st = transform_statements(f, *st);
            Statement::Loop(st)
        }
    };

    // Apply on the current statement
    f(st)
}

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
                let targets: Vec<(VecSerializer<ScalarValue>, &Statement)> = targets
                    .iter()
                    .map(|(values, st)| (VecSerializer::new(values), st))
                    .collect();
                let targets = VecSerializer::new(&targets);
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
            + Formatter<TypeDeclId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Statement::Assign(place, rvalue) => format!(
                "{}{} := {}",
                tab,
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            )
            .to_owned(),
            Statement::AssignGlobal(id, gid) => format!(
                "{}{} := {}",
                tab,
                ctx.format_object(*id),
                ctx.format_object(*gid),
            )
            .to_owned(),
            Statement::FakeRead(place) => {
                format!("{}@fake_read({})", tab, place.fmt_with_ctx(ctx)).to_owned()
            }
            Statement::SetDiscriminant(place, variant_id) => format!(
                "{}@discriminant({}) := {}",
                tab,
                place.fmt_with_ctx(ctx),
                variant_id.to_string()
            )
            .to_owned(),
            Statement::Drop(place) => format!("{}drop {}", tab, place.fmt_with_ctx(ctx)).to_owned(),
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
                    region_args,
                    type_args,
                    args,
                    dest,
                } = call;
                let call = fmt_call(ctx, func, region_args, type_args, args);
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
                        .map(|(pvl, st)| {
                            // Note that there may be several pattern values
                            let pvl: Vec<String> = pvl.iter().map(|v| v.to_string()).collect();
                            format!(
                                "{}{} => {{\n{}\n{}}}",
                                inner_tab1,
                                pvl.join(" | "),
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

pub(crate) struct FunDeclsFormatter<'ctx> {
    decls: &'ctx FunDecls,
}

pub(crate) struct GlobalDeclsFormatter<'ctx> {
    decls: &'ctx GlobalDecls,
}

impl<'ctx> FunDeclsFormatter<'ctx> {
    pub fn new(decls: &'ctx FunDecls) -> Self {
        FunDeclsFormatter { decls }
    }
}

impl<'ctx> Formatter<FunDeclId::Id> for FunDeclsFormatter<'ctx> {
    fn format_object(&self, id: FunDeclId::Id) -> String {
        let d = self.decls.get(id).unwrap();
        d.name.to_string()
    }
}

impl<'ctx> GlobalDeclsFormatter<'ctx> {
    pub fn new(decls: &'ctx GlobalDecls) -> Self {
        GlobalDeclsFormatter { decls }
    }
}

impl<'ctx> Formatter<GlobalDeclId::Id> for GlobalDeclsFormatter<'ctx> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        let d = self.decls.get(id).unwrap();
        d.name.to_string()
    }
}

impl<'ctx, FD, GD> Formatter<&Statement> for GAstFormatter<'ctx, FD, GD>
where
    Self: Formatter<FunDeclId::Id>,
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, st: &Statement) -> String {
        st.fmt_with_ctx(TAB_INCR, self)
    }
}

impl ExprBody {
    pub fn fmt_with_decls<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDecls,
        global_ctx: &'ctx GlobalDecls,
    ) -> String {
        let locals = Some(&self.locals);
        let fun_ctx = FunDeclsFormatter::new(fun_ctx);
        let global_ctx = GlobalDeclsFormatter::new(global_ctx);
        let ctx = GAstFormatter::new(ty_ctx, &fun_ctx, &global_ctx, None, locals);
        self.fmt_with_ctx(TAB_INCR, &ctx)
    }

    pub fn fmt_with_names<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDeclId::Vector<String>,
        global_ctx: &'ctx GlobalDeclId::Vector<String>,
    ) -> String {
        let locals = Some(&self.locals);
        let fun_ctx = FunNamesFormatter::new(fun_ctx);
        let global_ctx = GlobalNamesFormatter::new(global_ctx);
        let ctx = GAstFormatter::new(ty_ctx, &fun_ctx, &global_ctx, None, locals);
        self.fmt_with_ctx(TAB_INCR, &ctx)
    }

    pub fn fmt_with_ctx_names<'ctx>(&self, ctx: &CtxNames<'ctx>) -> String {
        self.fmt_with_names(&ctx.type_context, &ctx.fun_context, &ctx.global_context)
    }
}

impl FunDecl {
    pub fn fmt_with_ctx<'ctx, FD, GD>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FD,
        global_ctx: &'ctx GD,
    ) -> String
    where
        FD: Formatter<FunDeclId::Id>,
        GD: Formatter<GlobalDeclId::Id>,
    {
        // Initialize the contexts
        let fun_sig_ctx = FunSigFormatter {
            ty_ctx,
            sig: &self.signature,
        };

        let locals = match &self.body {
            None => None,
            Some(body) => Some(&body.locals),
        };

        let fmt_ctx = GAstFormatter::new(
            ty_ctx,
            fun_ctx,
            global_ctx,
            Some(&self.signature.type_params),
            locals,
        );

        // Use the contexts for printing
        self.gfmt_with_ctx("", &fun_sig_ctx, &fmt_ctx)
    }

    pub fn fmt_with_decls<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDecls,
        global_ctx: &'ctx GlobalDecls,
    ) -> String {
        let fun_ctx = FunDeclsFormatter::new(fun_ctx);
        let global_ctx = GlobalDeclsFormatter::new(global_ctx);
        self.fmt_with_ctx(ty_ctx, &fun_ctx, &global_ctx)
    }

    pub fn fmt_with_names<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDeclId::Vector<String>,
        global_ctx: &'ctx GlobalDeclId::Vector<String>,
    ) -> String {
        let fun_ctx = FunNamesFormatter::new(fun_ctx);
        let global_ctx = GlobalNamesFormatter::new(global_ctx);
        self.fmt_with_ctx(ty_ctx, &fun_ctx, &global_ctx)
    }

    pub fn fmt_with_ctx_names<'ctx>(&self, ctx: &CtxNames<'ctx>) -> String {
        self.fmt_with_names(&ctx.type_context, &ctx.fun_context, &ctx.global_context)
    }
}

impl GlobalDecl {
    pub fn fmt_with_ctx<'ctx, FD, GD>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FD,
        global_ctx: &'ctx GD,
    ) -> String
    where
        FD: Formatter<FunDeclId::Id>,
        GD: Formatter<GlobalDeclId::Id>,
    {
        let locals = match &self.body {
            None => None,
            Some(body) => Some(&body.locals),
        };

        let fmt_ctx = GAstFormatter::new(ty_ctx, fun_ctx, global_ctx, None, locals);

        // Use the contexts for printing
        self.gfmt_with_ctx("", &fmt_ctx)
    }

    pub fn fmt_with_decls<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDecls,
        global_ctx: &'ctx GlobalDecls,
    ) -> String {
        let fun_ctx = FunDeclsFormatter::new(fun_ctx);
        let global_ctx = GlobalDeclsFormatter::new(global_ctx);
        self.fmt_with_ctx(ty_ctx, &fun_ctx, &global_ctx)
    }

    pub fn fmt_with_names<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDeclId::Vector<String>,
        global_ctx: &'ctx GlobalDeclId::Vector<String>,
    ) -> String {
        let fun_ctx = FunNamesFormatter::new(fun_ctx);
        let global_ctx = GlobalNamesFormatter::new(global_ctx);
        self.fmt_with_ctx(ty_ctx, &fun_ctx, &global_ctx)
    }

    pub fn fmt_with_ctx_names<'ctx>(&self, ctx: &CtxNames<'ctx>) -> String {
        self.fmt_with_names(&ctx.type_context, &ctx.fun_context, &ctx.global_context)
    }
}
