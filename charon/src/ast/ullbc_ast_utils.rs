//! Implementations for [crate::ullbc_ast]
use crate::meta::Span;
use crate::ullbc_ast::*;
use std::mem;

impl SwitchTargets {
    pub fn get_targets(&self) -> Vec<BlockId> {
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
    pub fn new(span: Span, kind: StatementKind) -> Self {
        Statement {
            span,
            kind,
            comments_before: vec![],
        }
    }
}

impl Terminator {
    pub fn new(span: Span, kind: TerminatorKind) -> Self {
        Terminator {
            span,
            kind,
            comments_before: vec![],
        }
    }
    pub fn goto(span: Span, target: BlockId) -> Self {
        Self::new(span, TerminatorKind::Goto { target })
    }

    pub fn into_block(self) -> BlockData {
        BlockData {
            statements: vec![],
            terminator: self,
        }
    }
}

impl BlockData {
    /// Build a block that's just a goto terminator.
    pub fn new_goto(span: Span, target: BlockId) -> Self {
        BlockData {
            statements: vec![],
            terminator: Terminator::goto(span, target),
        }
    }

    pub fn targets(&self) -> Vec<BlockId> {
        match &self.terminator.kind {
            TerminatorKind::Goto { target } => {
                vec![*target]
            }
            TerminatorKind::Switch { targets, .. } => targets.get_targets(),
            TerminatorKind::Call {
                call: _,
                target,
                on_unwind,
            } => vec![*target, *on_unwind],
            TerminatorKind::Abort(..) | TerminatorKind::Return | TerminatorKind::UnwindResume => {
                vec![]
            }
        }
    }

    /// TODO: Write new documentation
    pub fn transform_operands<F: FnMut(&Span, &mut Vec<Statement>, &mut Operand)>(
        &mut self,
        mut f: F,
    ) {
        // Explore the operands in the statements
        for mut st in mem::take(&mut self.statements) {
            st.kind
                .dyn_visit_in_body_mut(|op: &mut Operand| f(&st.span, &mut self.statements, op));
            // Add the statement to the vector of statements
            self.statements.push(st)
        }

        // Explore the terminator
        self.terminator
            .kind
            .dyn_visit_in_body_mut(|op: &mut Operand| {
                f(&self.terminator.span, &mut self.statements, op)
            });
    }

    /// Apply a transformer to all the statements.
    ///
    /// The transformer should:
    /// - mutate the current statement in place
    /// - return the sequence of statements to introduce before the current statement
    pub fn transform<F: FnMut(&mut Statement) -> Vec<Statement>>(&mut self, mut f: F) {
        self.transform_sequences_bwd(|slice| {
            let new_statements = f(&mut slice[0]);
            if new_statements.is_empty() {
                vec![]
            } else {
                vec![(0, new_statements)]
            }
        });
    }

    /// Helper, see `transform_sequences_fwd` and `transform_sequences_bwd`.
    fn transform_sequences<F>(&mut self, mut f: F, forward: bool)
    where
        F: FnMut(&mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        let mut to_insert = vec![];
        let mut final_len = self.statements.len();
        if forward {
            for i in 0..self.statements.len() {
                let new_to_insert = f(&mut self.statements[i..]);
                to_insert.extend(new_to_insert.into_iter().map(|(j, stmts)| {
                    final_len += stmts.len();
                    (i + j, stmts)
                }));
            }
        } else {
            for i in (0..self.statements.len()).rev() {
                let new_to_insert = f(&mut self.statements[i..]);
                to_insert.extend(new_to_insert.into_iter().map(|(j, stmts)| {
                    final_len += stmts.len();
                    (i + j, stmts)
                }));
            }
        }
        if !to_insert.is_empty() {
            to_insert.sort_by_key(|(i, _)| *i);
            // Make it so the first element is always at the end so we can pop it.
            to_insert.reverse();
            // Construct the merged list of statements.
            let old_statements = mem::replace(&mut self.statements, Vec::with_capacity(final_len));
            for (i, stmt) in old_statements.into_iter().enumerate() {
                while let Some((j, _)) = to_insert.last()
                    && *j == i
                {
                    let (_, mut stmts) = to_insert.pop().unwrap();
                    self.statements.append(&mut stmts);
                }
                self.statements.push(stmt);
            }
        }
    }

    /// Apply a transformer to all the statements.
    ///
    /// The transformer should:
    /// - mutate the current statements in place
    /// - return a list of `(i, statements)` where `statements` will be inserted before index `i`.
    pub fn transform_sequences_fwd<F>(&mut self, f: F)
    where
        F: FnMut(&mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        self.transform_sequences(f, true);
    }

    /// Apply a transformer to all the statements.
    ///
    /// The transformer should:
    /// - mutate the current statements in place
    /// - return a list of `(i, statements)` where `statements` will be inserted before index `i`.
    pub fn transform_sequences_bwd<F>(&mut self, f: F)
    where
        F: FnMut(&mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        self.transform_sequences(f, false);
    }
}

impl ExprBody {
    pub fn transform_sequences_fwd<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Locals, &mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        for block in &mut self.body {
            block.transform_sequences_fwd(|seq| f(&mut self.locals, seq));
        }
    }

    pub fn transform_sequences_bwd<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Locals, &mut [Statement]) -> Vec<(usize, Vec<Statement>)>,
    {
        for block in &mut self.body {
            block.transform_sequences_bwd(|seq| f(&mut self.locals, seq));
        }
    }

    /// Apply a function to all the statements, in a bottom-up manner.
    pub fn visit_statements<F: FnMut(&mut Statement)>(&mut self, mut f: F) {
        for block in self.body.iter_mut().rev() {
            for st in block.statements.iter_mut().rev() {
                f(st);
            }
        }
    }
}

/// Helper to construct a small ullbc body.
pub struct BodyBuilder {
    /// The span to use for everything.
    pub span: Span,
    /// Body under construction.
    pub body: ExprBody,
    /// Block onto which we're adding statements. Its terminator is always `Return`.
    pub current_block: BlockId,
    /// Block to unwind to; created on demand.
    pub unwind_block: Option<BlockId>,
}

fn mk_block(span: Span, term: TerminatorKind) -> BlockData {
    BlockData {
        statements: vec![],
        terminator: Terminator::new(span, term),
    }
}

impl BodyBuilder {
    pub fn new(span: Span, arg_count: usize) -> Self {
        let mut body: ExprBody = GExprBody {
            span,
            locals: Locals::new(arg_count),
            comments: vec![],
            body: Vector::new(),
        };
        let current_block = body.body.push(BlockData {
            statements: Default::default(),
            terminator: Terminator::new(span, TerminatorKind::Return),
        });
        Self {
            span,
            body,
            current_block,
            unwind_block: None,
        }
    }

    /// Finalize the builder by returning the built body.
    pub fn build(self) -> ExprBody {
        self.body
    }

    /// Create a new local. Adds a `StorageLive` statement if the local is not one of the special
    /// ones (return or function argument).
    pub fn new_var(&mut self, name: Option<String>, ty: Ty) -> Place {
        let place = self.body.locals.new_var(name, ty);
        let local_id = place.as_local().unwrap();
        if !self.body.locals.is_return_or_arg(local_id) {
            self.push_statement(StatementKind::StorageLive(local_id));
        }
        place
    }

    /// Helper.
    fn current_block(&mut self) -> &mut BlockData {
        &mut self.body.body[self.current_block]
    }

    pub fn push_statement(&mut self, kind: StatementKind) {
        let st = Statement::new(self.span, kind);
        self.current_block().statements.push(st);
    }

    fn unwind_block(&mut self) -> BlockId {
        *self.unwind_block.get_or_insert_with(|| {
            self.body
                .body
                .push(mk_block(self.span, TerminatorKind::UnwindResume))
        })
    }

    pub fn call(&mut self, call: Call) {
        let next_block = self
            .body
            .body
            .push(mk_block(self.span, TerminatorKind::Return));
        let term = TerminatorKind::Call {
            target: next_block,
            call,
            on_unwind: self.unwind_block(),
        };
        self.current_block().terminator.kind = term;
        self.current_block = next_block;
    }
}
