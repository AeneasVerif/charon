//! Implementations for [crate::ullbc_ast]
#![allow(dead_code)]

use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
pub use crate::gast_utils::*;
use crate::meta::Meta;
use crate::types::*;
use crate::ullbc_ast::*;
use crate::values::*;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::iter::FromIterator;
use take_mut::take;

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
    pub fn new(meta: Meta, content: RawStatement) -> Self {
        Statement { meta, content }
    }

    /// Substitute the type variables and return the resulting statement.
    pub fn substitute(&self, subst: &ETypeSubst) -> Statement {
        let st = match &self.content {
            RawStatement::Assign(place, rvalue) => {
                RawStatement::Assign(place.substitute(subst), rvalue.substitute(subst))
            }
            RawStatement::FakeRead(place) => RawStatement::FakeRead(place.substitute(subst)),
            RawStatement::SetDiscriminant(place, variant_id) => {
                RawStatement::SetDiscriminant(place.substitute(subst), *variant_id)
            }
            RawStatement::StorageDead(var_id) => RawStatement::StorageDead(*var_id),
            RawStatement::Deinit(place) => RawStatement::Deinit(place.substitute(subst)),
        };

        Statement::new(self.meta, st)
    }
}

impl Terminator {
    pub fn new(meta: Meta, content: RawTerminator) -> Self {
        Terminator { meta, content }
    }

    /// Substitute the type variables and return the resulting terminator
    pub fn substitute(&self, subst: &ETypeSubst, cgsubst: &ConstGenericSubst) -> Terminator {
        let terminator = match &self.content {
            RawTerminator::Goto { target } => RawTerminator::Goto { target: *target },
            RawTerminator::Switch { discr, targets } => RawTerminator::Switch {
                discr: discr.substitute(subst),
                targets: targets.substitute(subst),
            },
            RawTerminator::Panic => RawTerminator::Panic,
            RawTerminator::Return => RawTerminator::Return,
            RawTerminator::Unreachable => RawTerminator::Unreachable,
            RawTerminator::Drop { place, target } => RawTerminator::Drop {
                place: place.substitute(subst),
                target: *target,
            },
            RawTerminator::Call { call, target } => {
                let Call {
                    func,
                    region_args,
                    type_args,
                    const_generic_args,
                    args,
                    dest,
                } = call;
                let call = Call {
                    func: func.clone(),
                    region_args: region_args.clone(),
                    type_args: type_args
                        .iter()
                        .map(|ty| ty.substitute_types(subst, cgsubst))
                        .collect(),
                    const_generic_args: const_generic_args
                        .iter()
                        .map(|cg| cg.substitute(&|var| cgsubst.get(var).unwrap().clone()))
                        .collect(),
                    args: Vec::from_iter(args.iter().map(|arg| arg.substitute(subst))),
                    dest: dest.substitute(subst),
                };
                RawTerminator::Call {
                    call,
                    target: *target,
                }
            }
            RawTerminator::Assert {
                cond,
                expected,
                target,
            } => RawTerminator::Assert {
                cond: cond.substitute(subst),
                expected: *expected,
                target: *target,
            },
        };

        Terminator::new(self.meta, terminator)
    }
}

impl BlockData {
    /// Substitute the type variables and return the resulting `BlockData`
    pub fn substitute(&self, subst: &ETypeSubst, cgsubst: &ConstGenericSubst) -> BlockData {
        let statements = self
            .statements
            .iter()
            .map(|x| x.substitute(subst))
            .collect();
        let terminator = self.terminator.substitute(subst, cgsubst);
        BlockData {
            statements,
            terminator,
        }
    }
}

impl Statement {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>,
    {
        match &self.content {
            RawStatement::Assign(place, rvalue) => format!(
                "{} := {}",
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            ),
            RawStatement::FakeRead(place) => {
                format!("@fake_read({})", place.fmt_with_ctx(ctx))
            }
            RawStatement::SetDiscriminant(place, variant_id) => format!(
                "@discriminant({}) := {}",
                place.fmt_with_ctx(ctx),
                variant_id
            ),
            RawStatement::StorageDead(vid) => {
                format!("@storage_dead({})", var_id_to_pretty_string(*vid))
            }
            RawStatement::Deinit(place) => {
                format!("@deinit({})", place.fmt_with_ctx(ctx))
            }
        }
    }
}

impl Terminator {
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
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
        match &self.content {
            RawTerminator::Goto { target } => format!("goto bb{target}"),
            RawTerminator::Switch { discr, targets } => match targets {
                SwitchTargets::If(true_block, false_block) => format!(
                    "if {} -> bb{} else -> bb{}",
                    discr.fmt_with_ctx(ctx),
                    true_block,
                    false_block
                ),
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(v, bid)| format!("{}: bb{}", v.to_string(), bid))
                        .collect();
                    maps.push(format!("otherwise: bb{otherwise}"));
                    let maps = maps.join(", ");

                    format!("switch {} -> {}", discr.fmt_with_ctx(ctx), maps)
                }
            },
            RawTerminator::Panic => "panic".to_string(),
            RawTerminator::Return => "return".to_string(),
            RawTerminator::Unreachable => "unreachable".to_string(),
            RawTerminator::Drop { place, target } => {
                format!("drop {} -> bb{}", place.fmt_with_ctx(ctx), target)
            }
            RawTerminator::Call { call, target } => {
                let Call {
                    func,
                    region_args,
                    type_args,
                    const_generic_args,
                    args,
                    dest,
                } = call;
                let call = fmt_call(ctx, func, region_args, type_args, const_generic_args, args);

                format!("{} := {} -> bb{}", dest.fmt_with_ctx(ctx), call, target,)
            }
            RawTerminator::Assert {
                cond,
                expected,
                target,
            } => format!(
                "assert({} == {}) -> bb{}",
                cond.fmt_with_ctx(ctx),
                expected,
                target
            ),
        }
    }
}

impl BlockData {
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
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
        let mut out: Vec<String> = Vec::new();

        // Format the statements
        for statement in &self.statements {
            out.push(format!("{}{};\n", tab, statement.fmt_with_ctx(ctx)).to_string());
        }

        // Format the terminator
        out.push(format!("{}{};", tab, self.terminator.fmt_with_ctx(ctx)));

        // Join the strings
        out.join("")
    }
}

fn fmt_body_blocks_with_ctx<'a, 'b, 'c, C>(
    body: &'a BlockId::Vector<BlockData>,
    tab: &'b str,
    ctx: &'c C,
) -> String
where
    C: Formatter<VarId::Id>
        + Formatter<TypeVarId::Id>
        + Formatter<&'a ErasedRegion>
        + Formatter<TypeDeclId::Id>
        + Formatter<ConstGenericVarId::Id>
        + Formatter<FunDeclId::Id>
        + Formatter<GlobalDeclId::Id>
        + Formatter<(TypeDeclId::Id, VariantId::Id)>
        + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
{
    let block_tab = format!("{tab}{TAB_INCR}");
    let mut blocks: Vec<String> = Vec::new();
    for (bid, block) in body.iter_indexed_values() {
        use crate::id_vector::ToUsize;
        blocks.push(
            format!(
                "{tab}bb{}: {{\n{}\n{tab}}}\n",
                bid.to_usize(),
                block.fmt_with_ctx(&block_tab, ctx),
            )
            .to_string(),
        );
    }
    blocks.join("\n")
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
        let ctx = GAstFormatter::new(ty_ctx, &fun_ctx, &global_ctx, None, locals, None);
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
        let ctx = GAstFormatter::new(ty_ctx, &fun_ctx, &global_ctx, None, locals, None);
        self.fmt_with_ctx(TAB_INCR, &ctx)
    }

    pub fn fmt_with_ctx_names(&self, ctx: &CtxNames<'_>) -> String {
        self.fmt_with_names(ctx.type_context, ctx.fun_context, ctx.global_context)
    }
}

pub(crate) struct FunDeclsFormatter<'ctx> {
    decls: &'ctx FunDecls,
}

pub(crate) struct GlobalDeclsFormatter<'ctx> {
    decls: &'ctx GlobalDecls,
}

impl<'ctx, FD, GD> Formatter<&Statement> for GAstFormatter<'ctx, FD, GD>
where
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, statement: &Statement) -> String {
        statement.fmt_with_ctx(self)
    }
}

impl<'ctx, FD, GD> Formatter<&BlockId::Vector<BlockData>> for GAstFormatter<'ctx, FD, GD>
where
    Self: Formatter<FunDeclId::Id>,
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, body: &BlockId::Vector<BlockData>) -> String {
        fmt_body_blocks_with_ctx(body, TAB_INCR, self)
    }
}

impl<'ctx, FD, GD> Formatter<&Terminator> for GAstFormatter<'ctx, FD, GD>
where
    Self: Formatter<FunDeclId::Id>,
    Self: Formatter<GlobalDeclId::Id>,
{
    fn format_object(&self, terminator: &Terminator) -> String {
        terminator.fmt_with_ctx(self)
    }
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

        let locals = self.body.as_ref().map(|body| &body.locals);
        let ctx = GAstFormatter::new(
            ty_ctx,
            fun_ctx,
            global_ctx,
            Some(&self.signature.type_params),
            locals,
            Some(&self.signature.const_generic_params),
        );

        // Use the contexts for printing
        self.gfmt_with_ctx("", &fun_sig_ctx, &ctx)
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

    pub fn fmt_with_ctx_names(&self, ctx: &CtxNames<'_>) -> String {
        self.fmt_with_names(ctx.type_context, ctx.fun_context, ctx.global_context)
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
        let locals = self.body.as_ref().map(|body| &body.locals);
        let ctx = GAstFormatter::new(ty_ctx, fun_ctx, global_ctx, None, locals, None);

        // Use the contexts for printing
        self.gfmt_with_ctx("", &ctx)
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

    pub fn fmt_with_ctx_names(&self, ctx: &CtxNames<'_>) -> String {
        self.fmt_with_names(ctx.type_context, ctx.fun_context, ctx.global_context)
    }
}

impl BlockData {
    /// Visit the operands in an rvalue and generate statements.
    /// Used below in [BlockData::transform_operands].
    fn transform_rvalue_operands<F: FnMut(&Meta, &mut Vec<Statement>, &mut Operand)>(
        meta: &Meta,
        nst: &mut Vec<Statement>,
        rval: &mut Rvalue,
        f: &mut F,
    ) {
        match rval {
            Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => f(meta, nst, op),
            Rvalue::BinaryOp(_, o1, o2) => {
                f(meta, nst, o1);
                f(meta, nst, o2);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    f(meta, nst, op);
                }
            }
            Rvalue::Global(_) | Rvalue::Discriminant(_) | Rvalue::Ref(_, _) | Rvalue::Len(_, _) => {
                // No operands: nothing to do
            }
        }
    }

    /// See [body_transform_operands]
    pub fn transform_operands<F: FnMut(&Meta, &mut Vec<Statement>, &mut Operand)>(
        mut self,
        f: &mut F,
    ) -> Self {
        // The new vector of statements
        let mut nst = vec![];

        // Explore the operands in the statements
        for mut st in self.statements {
            let meta = &st.meta;
            match &mut st.content {
                RawStatement::Assign(_, rvalue) => {
                    BlockData::transform_rvalue_operands(meta, &mut nst, rvalue, f);
                }
                RawStatement::FakeRead(_)
                | RawStatement::SetDiscriminant(_, _)
                | RawStatement::StorageDead(_)
                | RawStatement::Deinit(_) => {
                    // No operands: nothing to do
                }
            }
            // Add the statement to the vector of statements
            nst.push(st)
        }

        // Explore the terminator
        let meta = &self.terminator.meta;
        match &mut self.terminator.content {
            RawTerminator::Switch { discr, targets: _ } => {
                f(meta, &mut nst, discr);
            }
            RawTerminator::Call { call, target: _ } => {
                for arg in &mut call.args {
                    f(meta, &mut nst, arg);
                }
            }
            RawTerminator::Assert {
                cond,
                expected: _,
                target: _,
            } => {
                f(meta, &mut nst, cond);
            }
            RawTerminator::Panic
            | RawTerminator::Return
            | RawTerminator::Unreachable
            | RawTerminator::Goto { target: _ }
            | RawTerminator::Drop {
                place: _,
                target: _,
            } => {
                // Nothing to do
            }
        };

        // Update the vector of statements
        self.statements = nst;

        // Return
        self
    }
}

/// Transform a body by applying a function to its operands, and
/// inserting the statements generated by the operands at the end of the
/// block.
/// Useful to implement a pass on operands (see e.g., [crate::extract_global_assignments]).
///
/// The meta argument given to `f` is the meta argument of the [Terminator]
/// containing the operand. `f` should explore the operand it receives, and
/// push statements to the vector it receives as input.
pub fn body_transform_operands<F: FnMut(&Meta, &mut Vec<Statement>, &mut Operand)>(
    blocks: &mut BlockId::Vector<BlockData>,
    f: &mut F,
) {
    for block in blocks.iter_mut() {
        take(block, |b| b.transform_operands(f));
    }
}
