//! Implementations for [crate::llbc_ast]

use crate::llbc_ast::*;
use crate::meta;
use crate::meta::Span;
use derive_visitor::{visitor_fn_mut, DriveMut, Event};

/// Combine the span information from a [Switch]
pub fn combine_switch_targets_span(targets: &Switch) -> Span {
    match targets {
        Switch::If(_, st1, st2) => meta::combine_span(&st1.span, &st2.span),
        Switch::SwitchInt(_, _, branches, otherwise) => {
            let branches = branches.iter().map(|b| &b.1.span);
            let mbranches = meta::combine_span_iter(branches);
            meta::combine_span(&mbranches, &otherwise.span)
        }
        Switch::Match(_, branches, otherwise) => {
            let branches = branches.iter().map(|b| &b.1.span);
            let mbranches = meta::combine_span_iter(branches);
            if let Some(otherwise) = otherwise {
                meta::combine_span(&mbranches, &otherwise.span)
            } else {
                mbranches
            }
        }
    }
}

impl Switch {
    pub fn iter_targets(&self) -> impl Iterator<Item = &Block> {
        use itertools::Either;
        match self {
            Switch::If(_, exp1, exp2) => Either::Left([exp1, exp2].into_iter()),
            Switch::SwitchInt(_, _, targets, otherwise) => Either::Right(Either::Left(
                targets.iter().map(|(_, tgt)| tgt).chain([otherwise]),
            )),
            Switch::Match(_, targets, otherwise) => Either::Right(Either::Right(
                targets.iter().map(|(_, tgt)| tgt).chain(otherwise.as_ref()),
            )),
        }
    }

    pub fn iter_targets_mut(&mut self) -> impl Iterator<Item = &mut Block> {
        use itertools::Either;
        match self {
            Switch::If(_, exp1, exp2) => Either::Left([exp1, exp2].into_iter()),
            Switch::SwitchInt(_, _, targets, otherwise) => Either::Right(Either::Left(
                targets.iter_mut().map(|(_, tgt)| tgt).chain([otherwise]),
            )),
            Switch::Match(_, targets, otherwise) => Either::Right(Either::Right(
                targets
                    .iter_mut()
                    .map(|(_, tgt)| tgt)
                    .chain(otherwise.as_mut()),
            )),
        }
    }
}

impl Statement {
    pub fn new(span: Span, content: RawStatement) -> Self {
        Statement { span, content }
    }

    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
    }

    pub fn into_block(self) -> Block {
        Block {
            span: self.span,
            statements: vec![self],
        }
    }
}

impl Block {
    pub fn from_seq(seq: Vec<Statement>) -> Option<Self> {
        if seq.is_empty() {
            None
        } else {
            let span = seq
                .iter()
                .map(|st| st.span)
                .reduce(|a, b| meta::combine_span(&a, &b))
                .unwrap();
            Some(Block {
                span,
                statements: seq,
            })
        }
    }

    pub fn merge(mut self, mut other: Self) -> Self {
        self.span = meta::combine_span(&self.span, &other.span);
        self.statements.append(&mut other.statements);
        self
    }

    pub fn then(mut self, r: Statement) -> Self {
        self.span = meta::combine_span(&self.span, &r.span);
        self.statements.push(r);
        self
    }

    pub fn then_opt(self, other: Option<Statement>) -> Self {
        if let Some(other) = other {
            self.then(other)
        } else {
            self
        }
    }

    /// Apply a function to all the statements, in a bottom-up manner.
    pub fn visit_statements<F: FnMut(&mut Statement)>(&mut self, f: &mut F) {
        self.drive_mut(&mut visitor_fn_mut(|st: &mut Statement, e: Event| {
            if matches!(e, Event::Exit) {
                f(st)
            }
        }))
    }

    /// Apply a transformer to all the statements, in a bottom-up manner.
    ///
    /// The transformer should:
    /// - mutate the current statement in place
    /// - return the sequence of statements to introduce before the current statement
    pub fn transform<F: FnMut(&mut Statement) -> Vec<Statement>>(&mut self, f: &mut F) {
        self.drive_mut(&mut visitor_fn_mut(|blk: &mut Block, e: Event| {
            if matches!(e, Event::Exit) {
                for i in (0..blk.statements.len()).rev() {
                    let prefix_to_insert = f(&mut blk.statements[i]);
                    if !prefix_to_insert.is_empty() {
                        // Insert the new elements at index `i`. This only modifies `vec[i..]`
                        // so we can keep iterating `i` down as if nothing happened.
                        blk.statements.splice(i..i, prefix_to_insert);
                    }
                }
            }
        }))
    }

    /// Apply a transformer to all the statements, in a bottom-up manner. Compared to `transform`,
    /// this also gives access to the following statements if any. Statements that are not part of
    /// a sequence will be traversed as `[st]`. Statements that are will be traversed twice: once
    /// as `[st]`, and then as `[st, ..]` with the following statements if any.
    ///
    /// The transformer should:
    /// - mutate the current statements in place
    /// - return the sequence of statements to introduce before the current statements
    pub fn transform_sequences<F: FnMut(&mut [Statement]) -> Vec<Statement>>(&mut self, f: &mut F) {
        self.drive_mut(&mut visitor_fn_mut(|blk: &mut Block, e: Event| {
            if matches!(e, Event::Exit) {
                for i in (0..blk.statements.len()).rev() {
                    let prefix_to_insert = f(&mut blk.statements[i..]);
                    if !prefix_to_insert.is_empty() {
                        // Insert the new elements at index `i`. This only modifies `vec[i..]`
                        // so we can keep iterating `i` down as if nothing happened.
                        blk.statements.splice(i..i, prefix_to_insert);
                    }
                }
            }
        }))
    }
}
