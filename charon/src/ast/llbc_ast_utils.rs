//! Implementations for [crate::llbc_ast]

use crate::llbc_ast::{RawStatement, Statement, Switch};
use crate::meta;
use crate::meta::Span;
use derive_visitor::{visitor_fn_mut, DriveMut, Event};
use take_mut::take;

/// Goes from e.g. `(A; B; C) ; D` to `(A; (B; (C; D)))`. Statements in `firsts` must not be
/// sequences.
pub fn chain_statements(firsts: Vec<Statement>, last: Statement) -> Statement {
    if let Some(firsts) = Statement::from_seq(firsts) {
        firsts.then(last)
    } else {
        last
    }
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

    pub fn from_seq(seq: Vec<Statement>) -> Option<Statement> {
        if seq.is_empty() {
            None
        } else {
            let span = seq
                .iter()
                .map(|st| st.span)
                .reduce(|a, b| meta::combine_span(&a, &b))
                .unwrap();
            Some(Statement {
                span,
                content: RawStatement::Sequence(seq),
            })
        }
    }

    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
    }

    /// Builds a sequence from well-formed statements. Ensures that we don't incorrectly nest
    /// sequences. Must be used instead of the raw [RawStatement::Sequence] constructor.
    pub fn then(self, r: Statement) -> Statement {
        let span = meta::combine_span(&self.span, &r.span);

        let vec = if !self.content.is_sequence() && !r.content.is_sequence() {
            vec![self, r]
        } else {
            let mut l = self.into_sequence();
            let mut r = r.into_sequence();
            l.append(&mut r);
            l
        };

        Statement::new(span, RawStatement::Sequence(vec))
    }

    pub fn then_opt(self, other: Option<Statement>) -> Statement {
        if let Some(other) = other {
            self.then(other)
        } else {
            self
        }
    }

    /// If `self` is a sequence, return that sequence. Otherwise return `vec![self]`.
    pub fn into_sequence(self) -> Vec<Self> {
        match self.content {
            RawStatement::Sequence(vec) => vec,
            _ => vec![self],
        }
    }

    pub fn as_sequence_slice_mut(&mut self) -> &mut [Self] {
        match self.content {
            RawStatement::Sequence(ref mut vec) => vec.as_mut_slice(),
            _ => std::slice::from_mut(self),
        }
    }

    /// If `self` is a sequence that contains sequences, flatten the nesting. Use this when
    /// mutating a statement in a visitor if needed.
    pub fn flatten(&mut self) {
        if let RawStatement::Sequence(vec) = &self.content {
            if vec.iter().any(|st| st.content.is_sequence()) {
                take(&mut self.content, |rawst| {
                    RawStatement::Sequence(
                        rawst
                            .to_sequence()
                            .into_iter()
                            .flat_map(|st| st.into_sequence())
                            .collect(),
                    )
                })
            }
        }
    }

    /// Apply a transformer to all the statements, in a bottom-up manner.
    ///
    /// The transformer should:
    /// - mutate the current statement in place
    /// - return the sequence of statements to introduce before the current statement
    pub fn transform<F: FnMut(&mut Statement) -> Option<Vec<Statement>>>(&mut self, f: &mut F) {
        self.drive_mut(&mut visitor_fn_mut(|st: &mut Statement, e: Event| {
            if matches!(e, Event::Exit) {
                // Flatten any nested sequences created while traversing this statement..
                st.flatten();

                // Transform the current statement
                let prefix_seq = f(st);
                if let Some(prefix_seq) = prefix_seq && !prefix_seq.is_empty() {
                    take_mut::take(st, |st| chain_statements(prefix_seq, st))
                }
            }
        }));
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
        self.drive_mut(&mut visitor_fn_mut(|st: &mut Statement, e: Event| {
            if matches!(e, Event::Exit) {
                // Flatten any nested sequences created while traversing this statement..
                st.flatten();

                if let RawStatement::Sequence(seq) = &mut st.content {
                    for i in (0..seq.len()).rev() {
                        let prefix_to_insert = f(&mut seq[i..]);
                        if !prefix_to_insert.is_empty() {
                            // Insert the new elements at index `i`. This only modifies `vec[i..]`
                            // so we can keep iterating `i` down as if nothing happened.
                            seq.splice(i..i, prefix_to_insert);
                        }
                    }
                } else {
                    let prefix_to_insert = f(std::slice::from_mut(st));
                    if !prefix_to_insert.is_empty() {
                        take_mut::take(st, |st| chain_statements(prefix_to_insert, st))
                    }
                }
            }
        }));
    }
}
