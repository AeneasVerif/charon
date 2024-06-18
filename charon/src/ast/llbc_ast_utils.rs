//! Implementations for [crate::llbc_ast]

use crate::llbc_ast::{RawStatement, Statement, Switch};
use crate::meta;
use crate::meta::Span;
use derive_visitor::{DriveMut, VisitorMut};
use std::ops::DerefMut;
use take_mut::take;

/// Goes from e.g. `(A; B; C) ; D` to `(A; (B; (C; D)))`.
pub fn chain_statements(firsts: Vec<Statement>, last: Statement) -> Statement {
    firsts.into_iter().rev().fold(last, |cont, bind| {
        assert!(!bind.content.is_sequence());
        let span = meta::combine_span(&bind.span, &cont.span);
        Statement::new(span, RawStatement::Sequence(Box::new(bind), Box::new(cont)))
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
            let span = meta::combine_span(&l2.span, &r.span);
            Statement::new(span, RawStatement::Sequence(Box::new(l2), r))
        });
    }
}

/// Builds a sequence from well-formed statements.
/// Ensures that the left statement will not be a sequence in the new sequence:
/// Must be used instead of the raw [RawStatement::Sequence] constructor,
/// unless you're sure that the left statement is not a sequence.
pub fn new_sequence(mut l: Statement, r: Statement) -> Statement {
    let span = meta::combine_span(&l.span, &r.span);

    let r = Box::new(r);
    let nst = match l.content {
        RawStatement::Sequence(_, _) => {
            append_rightmost(&mut l, r);
            l.content
        }
        lc => RawStatement::Sequence(Box::new(Statement::new(l.span, lc)), r),
    };

    Statement::new(span, nst)
}

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
    pub fn new(span: Span, content: RawStatement) -> Self {
        Statement { span, content }
    }

    /// Collect the statements this is made up of into a vec. If `self` is not a sequence, the vec
    /// will be `vec![self]`.
    pub fn sequence_to_vec(self) -> Vec<Self> {
        fn collect_to_vec(x: Statement, vec: &mut Vec<Statement>) {
            match x.content {
                RawStatement::Sequence(a, b) => {
                    assert!(!a.content.is_sequence());
                    vec.push(*a);
                    collect_to_vec(*b, vec);
                }
                _ => vec.push(x),
            }
        }
        let mut vec = Vec::new();
        collect_to_vec(self, &mut vec);
        vec
    }

    /// If `self` is a sequence whose first component is a sequence, refold the statements to
    /// repair the invariant on sequences. All otehr sequences are expected to respect the
    /// invariant. Use this when mutating a statement in a visitor if needed.
    pub fn reparenthesize(&mut self) {
        if let RawStatement::Sequence(st1, _) = &mut self.content {
            if st1.content.is_sequence() {
                // We did mess up the parenthesization. Fix it.
                take(self, |st| {
                    let (st1, st2) = st.content.to_sequence();
                    let st1 = st1.sequence_to_vec();
                    chain_statements(st1, *st2)
                })
            }
        }
    }
}

/// Helper for [transform_statements]
#[derive(VisitorMut)]
#[visitor(Statement(exit))]
struct TransformStatements<'a, F: FnMut(&mut Statement) -> Option<Vec<Statement>>> {
    tr: &'a mut F,
}

impl<'a, F> TransformStatements<'a, F>
where
    F: FnMut(&mut Statement) -> Option<Vec<Statement>>,
{
    fn exit_statement(&mut self, st: &mut Statement) {
        // Reparenthesize sequences we messed up while traversing.
        st.reparenthesize();

        // Transform the current statement
        let st_seq = (self.tr)(st);
        if let Some(seq) = st_seq && !seq.is_empty() {
            take(st, |st| chain_statements(seq, st))
        }
    }
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
        self.drive_mut(&mut visitor);
    }
}
