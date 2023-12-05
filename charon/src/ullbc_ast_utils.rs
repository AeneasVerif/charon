//! Implementations for [crate::ullbc_ast]
use crate::common::TAB_INCR;
use crate::formatter::AstFormatter;
pub use crate::gast_utils::*;
use crate::meta::Meta;
use crate::types::*;
use crate::ullbc_ast::*;
use crate::values::*;
use macros::make_generic_in_borrows;
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
}

impl Statement {
    pub fn new(meta: Meta, content: RawStatement) -> Self {
        Statement { meta, content }
    }
}

impl Terminator {
    pub fn new(meta: Meta, content: RawTerminator) -> Self {
        Terminator { meta, content }
    }
}

impl Statement {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
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
                format!("@storage_dead({})", vid.to_pretty_string())
            }
            RawStatement::Deinit(place) => {
                format!("@deinit({})", place.fmt_with_ctx(ctx))
            }
        }
    }
}

impl Terminator {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
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
                let (call_s, _) = fmt_call(ctx, call);
                format!("{} := {call_s} -> bb{target}", call.dest.fmt_with_ctx(ctx),)
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
    pub fn fmt_with_ctx<C>(&self, tab: &str, ctx: &C) -> String
    where
        C: AstFormatter,
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

pub(crate) fn fmt_body_blocks_with_ctx<C>(
    body: &BlockId::Vector<BlockData>,
    tab: &str,
    ctx: &C,
) -> String
where
    C: AstFormatter,
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

impl FunDecl {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        self.gfmt_with_ctx("", ctx)
    }
}

impl GlobalDecl {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        self.gfmt_with_ctx("", ctx)
    }
}

impl BlockData {
    /// Visit the operands in an rvalue and generate statements.
    /// Used below in [BlockData::transform_operands].
    /// TODO: use visitors
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
            Rvalue::Repeat(op, _, _) => {
                f(meta, nst, op);
            }
            Rvalue::Global(_) | Rvalue::Discriminant(_) | Rvalue::Ref(_, _) | Rvalue::Len(..) => {
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

// Derive two implementations at once: one which uses shared borrows, and one
// which uses mutable borrows.
// Generates the traits: `SharedAstVisitor` and `MutAstVisitor`.
make_generic_in_borrows! {

/// A visitor for the ULLBC AST
///
/// Remark: we can't call the "super" method when reimplementing a method
/// (unlike what can be done in, say, OCaml). This makes imlementing visitors
/// slightly awkward, and is the reason why we split some visit functions in two:
/// a "standard" version to be overriden, and a "default" version which should
/// not be overriden and gives access to the "super" method.
///
/// TODO: implement macros to automatically derive visitors.
pub trait AstVisitor: crate::expressions::ExprVisitor {
    fn visit_block_data(&mut self, block: &BlockData) {
        for st in &block.statements {
            self.visit_statement(st);
        }
        self.visit_terminator(&block.terminator);
    }

    fn visit_statement(&mut self, st: &Statement) {
        self.visit_meta(&st.meta);
        self.visit_raw_statement(&st.content);
    }

    fn visit_raw_statement(&mut self, st: &RawStatement) {
        self.default_visit_raw_statement(st);
    }

    fn default_visit_raw_statement(&mut self, st: &RawStatement) {
        use RawStatement::*;
        match st {
            Assign(p, rv) => self.visit_assign(p, rv),
            FakeRead(p) => self.visit_fake_read(p),
            SetDiscriminant(p, vid) => self.visit_set_discriminant(p, vid),
            StorageDead(vid) => self.visit_storage_dead(vid),
            Deinit(p) => self.visit_deinit(p),
        }
    }

    fn visit_assign(&mut self, p: &Place, rv: &Rvalue) {
        self.visit_place(p);
        self.visit_rvalue(rv);
    }

    fn visit_fake_read(&mut self, p: &Place) {
        self.visit_place(p);
    }

    fn visit_set_discriminant(&mut self, p: &Place, _vid: &VariantId::Id) {
        self.visit_place(p);
    }

    fn visit_storage_dead(&mut self, vid: &VarId::Id) {
        self.visit_var_id(vid);
    }

    fn visit_deinit(&mut self, p: &Place) {
        self.visit_place(p);
    }

    fn visit_terminator(&mut self, st: &Terminator) {
        self.visit_meta(&st.meta);
        self.visit_raw_terminator(&st.content);
    }

    fn visit_meta(&mut self, st: &Meta) {}

    fn default_visit_raw_terminator(&mut self, st: &RawTerminator) {
        use RawTerminator::*;
        match st {
            Goto { target } => self.visit_goto(target),
            Switch { discr, targets } => {
                self.visit_switch(discr, targets);
            }
            Panic => self.visit_panic(),
            Return => self.visit_return(),
            Unreachable => self.visit_unreachable(),
            Drop { place, target } => {
                self.visit_drop(place, target);
            }
            Call { call, target } => {
                self.visit_call_statement(call, target);
            }
            Assert {
                cond,
                expected,
                target,
            } => {
                self.visit_assert(cond, expected, target);
            }
        }
    }

    fn visit_raw_terminator(&mut self, st: &RawTerminator) {
        self.default_visit_raw_terminator(st);
    }

    fn visit_goto(&mut self, target: &BlockId::Id) {
        self.visit_block_id(target)
    }

    fn visit_switch(&mut self, discr: &Operand, targets: &SwitchTargets) {
        self.visit_operand(discr);
        self.visit_switch_targets(targets);
    }

    fn visit_panic(&mut self) {}

    fn visit_return(&mut self) {}

    fn visit_unreachable(&mut self) {}

    fn visit_drop(&mut self, place: &Place, target: &BlockId::Id) {
        self.visit_place(place);
        self.visit_block_id(target);
    }

    fn visit_call_statement(&mut self, call: &Call, target: &BlockId::Id) {
        self.visit_call(call);
        self.visit_block_id(target);
    }

    fn visit_assert(&mut self, cond: &Operand, expected: &bool, target: &BlockId::Id) {
        self.visit_operand(cond);
        self.visit_block_id(target);
    }

    fn visit_block_id(&mut self, id: &BlockId::Id) {}

    fn visit_switch_targets(&mut self, targets: &SwitchTargets) {
        use SwitchTargets::*;
        match targets {
            If(then_id, else_id) => self.visit_if(then_id, else_id),
            SwitchInt(int_ty, branches, otherwise) => {
                self.visit_switch_int(int_ty, branches, otherwise)
            }
        }
    }

    fn visit_if(&mut self, then_id: &BlockId::Id, else_id: &BlockId::Id) {
        self.visit_block_id(then_id);
        self.visit_block_id(else_id);
    }

    fn visit_switch_int(
        &mut self,
        int_ty: &IntegerTy,
        branches: &Vec<(ScalarValue, BlockId::Id)>,
        otherwise: &BlockId::Id,
    ) {
        for (_, br) in branches {
            self.visit_block_id(br);
        }
        self.visit_block_id(otherwise);
    }
}

} // make_generic_in_borrows
