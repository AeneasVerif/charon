//! Implementations for [crate::llbc_ast]

use crate::expressions::{MutExprVisitor, Operand, Place, Rvalue};
use crate::llbc_ast::{Assert, RawStatement, Statement, Switch};
use crate::meta;
use crate::meta::Meta;
use crate::types::*;
use crate::values::*;
use macros::make_generic_in_borrows;
use std::ops::DerefMut;
use take_mut::take;

/// Goes from e.g. `(A; B; C) ; D` to `(A; (B; (C; D)))`.
pub fn chain_statements(firsts: Vec<Statement>, last: Statement) -> Statement {
    firsts.into_iter().rev().fold(last, |cont, bind| {
        assert!(!bind.content.is_sequence());
        let meta = meta::combine_meta(&bind.meta, &cont.meta);
        Statement::new(meta, RawStatement::Sequence(Box::new(bind), Box::new(cont)))
    })
}

/// Utility function for [new_sequence].
/// Efficiently appends a new statement at the rightmost place of a well-formed sequence.
fn append_rightmost(seq: &mut Statement, r: Box<Statement>) {
    let (_l1, l2) = match &mut seq.content {
        RawStatement::Sequence(l1, l2) => (l1, l2),
        _ => unreachable!(),
    };
    if l2.content.is_sequence() {
        append_rightmost(l2, r);
    } else {
        take(l2.deref_mut(), move |l2| {
            let meta = meta::combine_meta(&l2.meta, &r.meta);
            Statement::new(meta, RawStatement::Sequence(Box::new(l2), r))
        });
    }
}

/// Builds a sequence from well-formed statements.
/// Ensures that the left statement will not be a sequence in the new sequence:
/// Must be used instead of the raw [RawStatement::Sequence] constructor,
/// unless you're sure that the left statement is not a sequence.
pub fn new_sequence(mut l: Statement, r: Statement) -> Statement {
    let meta = meta::combine_meta(&l.meta, &r.meta);

    let r = Box::new(r);
    let nst = match l.content {
        RawStatement::Sequence(_, _) => {
            append_rightmost(&mut l, r);
            l.content
        }
        lc => RawStatement::Sequence(Box::new(Statement::new(l.meta, lc)), r),
    };

    Statement::new(meta, nst)
}

/// Combine the meta information from a [Switch]
pub fn combine_switch_targets_meta(targets: &Switch) -> Meta {
    match targets {
        Switch::If(_, st1, st2) => meta::combine_meta(&st1.meta, &st2.meta),
        Switch::SwitchInt(_, _, branches, otherwise) => {
            let branches = branches.iter().map(|b| &b.1.meta);
            let mbranches = meta::combine_meta_iter(branches);
            meta::combine_meta(&mbranches, &otherwise.meta)
        }
        Switch::Match(_, branches, otherwise) => {
            let branches = branches.iter().map(|b| &b.1.meta);
            let mbranches = meta::combine_meta_iter(branches);
            if let Some(otherwise) = otherwise {
                meta::combine_meta(&mbranches, &otherwise.meta)
            } else {
                mbranches
            }
        }
    }
}

impl Switch {
    pub fn get_targets(&self) -> Vec<&Statement> {
        match self {
            Switch::If(_, exp1, exp2) => {
                vec![exp1, exp2]
            }
            Switch::SwitchInt(_, _, targets, otherwise) => {
                let mut out: Vec<&Statement> = vec![];
                for (_, tgt) in targets {
                    out.push(tgt);
                }
                out.push(otherwise);
                out
            }
            Switch::Match(_, targets, otherwise) => {
                let mut out: Vec<&Statement> = vec![];
                for (_, tgt) in targets {
                    out.push(tgt);
                }
                if let Some(otherwise) = otherwise {
                    out.push(otherwise);
                }
                out
            }
        }
    }
}

impl Statement {
    pub fn new(meta: Meta, content: RawStatement) -> Self {
        Statement { meta, content }
    }
}

// Derive two implementations at once: one which uses shared borrows, and one
// which uses mutable borrows.
// Generates the traits: `SharedAstVisitor` and `MutAstVisitor`.
make_generic_in_borrows! {

/// A visitor for the LLBC AST
///
/// Remark: we can't call the "super" method when reimplementing a method
/// (unlike what can be done in, say, OCaml). This makes imlementing visitors
/// slightly awkward, and is the reason why we split some visit functions in two:
/// a "standard" version to be overriden, and a "default" version which should
/// not be overriden and gives access to the "super" method.
///
/// TODO: implement macros to automatically derive visitors.
/// TODO: explore all the types
pub trait AstVisitor: crate::expressions::ExprVisitor {
    /// Spawn the visitor (used for the branchings)
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self));

    /// We call this function right after we explored all the branches
    /// in a branching.
    fn merge(&mut self);

    fn default_visit_statement(&mut self, st: &Statement) {
        self.visit_meta(&st.meta);
        self.visit_raw_statement(&st.content)
    }

    fn visit_statement(&mut self, st: &Statement) {
        self.default_visit_statement(st)
    }

    fn visit_meta(&mut self, st: &Meta) {}

    fn default_visit_raw_statement(&mut self, st: &RawStatement) {
        match st {
            RawStatement::Assign(p, rv) => {
                self.visit_assign(p, rv);
            }
            RawStatement::FakeRead(p) => {
                self.visit_fake_read(p);
            }
            RawStatement::SetDiscriminant(p, vid) => {
                self.visit_set_discriminant(p, vid);
            }
            RawStatement::Drop(p) => {
                self.visit_drop(p);
            }
            RawStatement::Assert(a) => {
                self.visit_assert(a);
            }
            RawStatement::Call(c) => {
                self.visit_call(c);
            }
            RawStatement::Panic => {
                self.visit_panic();
            }
            RawStatement::Return => self.visit_return(),
            RawStatement::Break(i) => {
                self.visit_break(i);
            }
            RawStatement::Continue(i) => {
                self.visit_continue(i);
            }
            RawStatement::Nop => self.visit_nop(),
            RawStatement::Sequence(st1, st2) => self.visit_sequence(st1, st2),
            RawStatement::Switch(s) => self.visit_switch(s),
            RawStatement::Loop(lp) => self.visit_loop(lp),
        }
    }

    fn visit_raw_statement(&mut self, st: &RawStatement) {
        self.default_visit_raw_statement(st);
    }

    fn visit_assign(&mut self, p: &Place, rv: &Rvalue) {
        self.visit_place(p);
        self.visit_rvalue(rv)
    }

    fn visit_fake_read(&mut self, p: &Place) {
        self.visit_place(p);
    }

    fn visit_set_discriminant(&mut self, p: &Place, _: &VariantId) {
        self.visit_place(p);
    }

    fn visit_drop(&mut self, p: &Place) {
        self.visit_place(p);
    }

    fn visit_assert(&mut self, a: &Assert) {
        self.visit_operand(&a.cond);
    }

    fn visit_panic(&mut self) {}
    fn visit_return(&mut self) {}
    fn visit_break(&mut self, _: &usize) {}
    fn visit_continue(&mut self, _: &usize) {}
    fn visit_nop(&mut self) {}

    fn visit_sequence(&mut self, st1: &Statement, st2: &Statement) {
        self.visit_statement(st1);
        self.visit_statement(st2);
    }

    fn default_visit_switch(&mut self, s: &Switch) {
        match s {
            Switch::If(scrut, then_branch, else_branch) => {
                self.visit_if(scrut, then_branch, else_branch)
            }
            Switch::SwitchInt(scrut, int_ty, branches, otherwise) => {
                self.visit_switch_int(scrut, int_ty, branches, otherwise)
            }
            Switch::Match(scrut, branches, otherwise) => {
                self.visit_match(scrut, branches, otherwise)
            }
        }
    }

    fn visit_switch(&mut self, s: &Switch) {
        self.default_visit_switch(s)
    }

    fn visit_if(&mut self, scrut: &Operand, then_branch: &Statement, else_branch: &Statement) {
        self.visit_operand(scrut);
        self.spawn(&mut |v| v.visit_statement(then_branch));
        self.spawn(&mut |v| v.visit_statement(else_branch));
        self.merge();
    }

    fn visit_switch_int(
        &mut self,
        scrut: &Operand,
        _: &IntegerTy,
        branches: &Vec<(Vec<ScalarValue>, Statement)>,
        otherwise: &Statement,
    ) {
        self.visit_operand(scrut);
        for (_, st) in branches {
            self.spawn(&mut |v| v.visit_statement(st));
        }
        self.spawn(&mut |v| v.visit_statement(otherwise));
        self.merge();
    }

    fn visit_match(
        &mut self,
        scrut: &Place,
        branches: &Vec<(Vec<VariantId>, Statement)>,
        otherwise: &Option<Box<Statement>>,
    ) {
        self.visit_place(scrut);
        for (_, st) in branches {
            self.spawn(&mut |v| v.visit_statement(st));
        }
        if let Some(otherwise) = otherwise {
            self.spawn(&mut |v| v.visit_statement(otherwise));
        }
        self.merge();
    }

    fn visit_loop(&mut self, lp: &Statement) {
        self.visit_statement(lp)
    }
}

} // make_generic_in_borrows

/// Helper for [transform_statements]
struct TransformStatements<'a, F: FnMut(&mut Statement) -> Option<Vec<Statement>>> {
    tr: &'a mut F,
}

impl<'a, F: FnMut(&mut Statement) -> Option<Vec<Statement>>> MutTypeVisitor
    for TransformStatements<'a, F>
{
}
impl<'a, F: FnMut(&mut Statement) -> Option<Vec<Statement>>> MutExprVisitor
    for TransformStatements<'a, F>
{
}

impl<'a, F: FnMut(&mut Statement) -> Option<Vec<Statement>>> MutAstVisitor
    for TransformStatements<'a, F>
{
    fn visit_statement(&mut self, st: &mut Statement) {
        match &mut st.content {
            RawStatement::Sequence(st1, st2) => {
                // Bottom-up
                self.visit_statement(st2);
                self.default_visit_raw_statement(&mut st1.content);

                // Transform the current statement
                let st_seq = (self.tr)(st1);
                if let Some(seq) = st_seq && !seq.is_empty() {
                    take(st, |st| chain_statements(seq, st))
                }
                // TODO: we might want to apply tr to the whole resulting sequence
            }
            _ => {
                // Bottom-up
                self.default_visit_raw_statement(&mut st.content);

                // Transform the current statement
                let st_seq = (self.tr)(st);
                if let Some(seq) = st_seq && !seq.is_empty() {
                    take(st, |st| chain_statements(seq, st))
                }
            }
        }
    }

    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}
}

impl Statement {
    /// Apply a transformer to all the statements, in a bottom-up manner.
    ///
    /// The transformer should:
    /// - mutate the current statement in place
    /// - return the sequence of statements to introduce before the current statement
    ///
    /// We do the transformation in such a way that the
    /// sequences of statements are properly chained. In particuliar,
    /// if in `s1; s2` we transform `s1` to the sequence `s1_1; s1_2`,
    /// then the resulting statement is `s1_1; s1_2; s2` and **not**
    /// `{ s1_1; s1_2 }; s2`.
    pub fn transform<F: FnMut(&mut Statement) -> Option<Vec<Statement>>>(&mut self, f: &mut F) {
        let mut visitor = TransformStatements { tr: f };
        visitor.visit_statement(self);
    }
}
