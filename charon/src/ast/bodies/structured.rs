//! Bodies with structured control-flow (`if ... then ... else ...`,
//! `loop { ... }`, etc).
//!
//! We reconstruct this structure from the unstructured ast in an optional translation pass.
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde_state::{DeserializeState, SerializeState};
use std::mem;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::ast::*;

// Globally-unique identifier for each statement.
generate_index_type!(StatementId);
// Globally-unique identifier for each block.
generate_index_type!(BlockId);

pub type ExprBody = GExprBody<Block>;

/// A sequence of statements.
#[derive(Debug, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(state_implements = HashConsSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct Block {
    pub span: Span,
    /// Integer uniquely identifying this block. To simplify things we generate globally-fresh ids
    /// when creating a new `Block`.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("block_id"))]
    pub id: BlockId,
    pub statements: Vec<Statement>,
}

/// A statement, which can contain nested statements inside loops or switchers.
#[derive(Debug, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct Statement {
    pub span: Span,
    /// Integer uniquely identifying this statement among the statmeents in the current body. To
    /// simplify things we generate globally-fresh ids when creating a new `Statement`.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("statement_id"))]
    pub id: StatementId,
    pub kind: StatementKind,
    /// Comments that precede this statement.
    // This is filled in a late pass after all the control-flow manipulation.
    pub comments_before: Vec<String>,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    EnumIsA,
    EnumToGetters,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum StatementKind {
    /// Assigns an `Rvalue` to a `Place`. e.g. `let y = x;` could become
    /// `y := move x` which is represented as `Assign(y, Rvalue::Use(Operand::Move(x)))`.
    Assign(Place, Rvalue),
    /// Not used today because we take MIR built.
    SetDiscriminant(Place, VariantId),
    /// Indicates that this local should be allocated; if it is already allocated, this frees
    /// the local and re-allocates it. The arguments do not receive a `StorageLive`. We ensure in
    /// the micro-pass `insert_storage_statements` that all other locals have a `StorageLive`
    /// associated with them.
    StorageLive(LocalId),
    /// Deallocates the given local; if it is already deallocated, this is
    /// a no-op. Not all local deallocations are explicit: if a non-return local is still live at
    /// function end (return or unwind), it is implicitly deallocated.
    /// If `--deallocate-all-locals` is set, all local deallocations are made explicit.
    StorageDead(LocalId),
    /// A place is mentioned, but not accessed. The place itself must still be valid though, so
    /// this statement is not a no-op: it can trigger UB if the place's projections are not valid
    /// (e.g. because they go out of bounds).
    PlaceMention(Place),
    /// Statements that only affect borrow-checking.
    Borrowck(BorrowckStatement),
    /// Drop the value at the given place.
    ///
    /// Depending on `DropKind`, this may be a real call to `drop_glue`, or a conditional call
    /// that should only happen if the place has not been moved out of. See the docs of `DropKind`
    /// for more details; to get precise drops use `--precise-drops`.
    Drop {
        place: Place,
        /// Reference to the `drop_glue` code to call on drop.
        fn_ptr: FnPtr,
        kind: DropKind,
        on_unwind: Block,
    },
    Assert {
        assert: Assert,
        on_failure: AbortKind,
        on_unwind: Block,
    },
    /// An inline assembly block. For now we only preserve the template string.
    InlineAsm {
        asm: String,
        targets: Vec<Block>,
        on_unwind: Block,
    },
    Call {
        call: Call,
        on_unwind: Block,
    },
    /// Panic also handles "unreachable". We keep the name of the panicking function that was
    /// called.
    Abort(AbortKind),
    Return,
    /// Unwind out of the current function into its caller.
    UnwindResume,
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
    Switch(Switch),
    Loop(Block),
    Error(String),
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    EnumIsA,
    EnumToGetters,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    VariantName,
    VariantIndexArity,
)]
pub enum Switch {
    /// Gives the `if` block and the `else` block. The `Operand` is the condition of the `if`, e.g. `if (y == 0)` could become
    /// ```text
    /// v@3 := copy y; // Represented as `Assign(v@3, Use(Copy(y))`
    /// v@2 := move v@3 == 0; // Represented as `Assign(v@2, BinOp(BinOp::Eq, Move(y), Const(0)))`
    /// if (move v@2) { // Represented as `If(Move(v@2), <then branch>, <else branch>)`
    /// ```
    If(Operand, Block, Block),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    /// Also, we use a `Vec` to make sure the order of the switch
    /// branches is preserved.
    ///
    /// Rk.: we use a vector of values, because some of the branches may
    /// be grouped together, like for the following code:
    /// ```text
    /// match e {
    ///   E::V1 | E::V2 => ..., // Grouped
    ///   E::V3 => ...
    /// }
    /// ```
    SwitchInt(Operand, LiteralTy, Vec<(Vec<Literal>, Block)>, Block),
    /// A match over an ADT.
    ///
    /// The match statement is introduced in [crate::transform::resugar::reconstruct_matches]
    /// (whenever we find a discriminant read, we merge it with the subsequent
    /// switch into a match).
    Match(Place, Vec<(Vec<VariantId>, Block)>, Option<Block>),
}

/// Ignores statement ids.
impl PartialEq for Statement {
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span
            && self.kind == other.kind
            && self.comments_before == other.comments_before
    }
}

/// Ignores block ids.
impl PartialEq for Block {
    fn eq(&self, other: &Self) -> bool {
        self.span == other.span && self.statements == other.statements
    }
}

impl Block {
    pub fn new(span: Span, statements: Vec<Statement>) -> Self {
        Block {
            span,
            id: BlockId::fresh(),
            statements,
        }
    }

    pub fn new_abort(span: Span, kind: AbortKind) -> Self {
        Statement::new(span, StatementKind::Abort(kind)).into_block()
    }

    pub fn new_unreachable(span: Span) -> Self {
        Self::new_abort(span, AbortKind::UndefinedBehavior)
    }

    pub fn from_seq(seq: Vec<Statement>) -> Option<Self> {
        if seq.is_empty() {
            None
        } else {
            let span = seq
                .iter()
                .map(|st| st.span)
                .reduce(|a, b| meta::combine_span(&a, &b))
                .unwrap();
            Some(Block::new(span, seq))
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

    /// Apply a function to all the statements, in a top-down manner.
    pub fn visit_statements<F: FnMut(&mut Statement)>(&mut self, f: F) {
        self.visit_helper(|_| {}, f);
    }

    /// Apply a transformer to all the statements, in a bottom-up manner. Compared to `transform`,
    /// this also gives access to the following statements if any. Statements that are not part of
    /// a sequence will be traversed as `[st]`. Statements that are will be traversed twice: once
    /// as `[st]`, and then as `[st, ..]` with the following statements if any.
    ///
    /// The transformer should:
    /// - mutate the current statements in place
    /// - return the sequence of statements to introduce before the current statements
    pub fn transform_sequences<F: FnMut(&mut [Statement]) -> Vec<Statement>>(&mut self, mut f: F) {
        self.visit_blocks_bwd(|blk: &mut Block| {
            let mut final_len = blk.statements.len();
            let mut to_insert = vec![];
            for i in (0..blk.statements.len()).rev() {
                let new_to_insert = f(&mut blk.statements[i..]);
                final_len += new_to_insert.len();
                to_insert.push((i, new_to_insert));
            }
            if !to_insert.is_empty() {
                to_insert.sort_by_key(|(i, _)| *i);
                // Make it so the first element is always at the end so we can pop it.
                to_insert.reverse();
                // Construct the merged list of statements.
                let old_statements =
                    mem::replace(&mut blk.statements, Vec::with_capacity(final_len));
                for (i, stmt) in old_statements.into_iter().enumerate() {
                    while let Some((j, _)) = to_insert.last()
                        && *j == i
                    {
                        let (_, mut stmts) = to_insert.pop().unwrap();
                        blk.statements.append(&mut stmts);
                    }
                    blk.statements.push(stmt);
                }
            }
        })
    }

    /// Visit `self` and its sub-blocks in a bottom-up (post-order) traversal.
    pub fn visit_blocks_bwd<F: FnMut(&mut Block)>(&mut self, f: F) {
        self.visit_helper(f, |_| {});
    }

    /// Small visitor helper to visit statements and blocks.
    fn visit_helper<F: FnMut(&mut Block), G: FnMut(&mut Statement)>(
        &mut self,
        exit_blk: F,
        enter_stmt: G,
    ) {
        #[derive(Visitor)]
        pub struct BlockVisitor<F: FnMut(&mut Block), G: FnMut(&mut Statement)> {
            exit_blk: F,
            enter_stmt: G,
        }

        impl<F: FnMut(&mut Block), G: FnMut(&mut Statement)> VisitBodyMut for BlockVisitor<F, G> {
            fn exit_llbc_block(&mut self, x: &mut Block) {
                (self.exit_blk)(x)
            }
            fn enter_llbc_statement(&mut self, x: &mut Statement) {
                (self.enter_stmt)(x)
            }
        }
        BlockVisitor {
            exit_blk,
            enter_stmt,
        }
        .visit_by_val_infallible(self);
    }
}

impl BlockId {
    pub fn fresh() -> BlockId {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        BlockId::new(id)
    }
}

impl Statement {
    pub fn new(span: Span, kind: StatementKind) -> Self {
        Statement {
            span,
            id: StatementId::fresh(),
            kind,
            comments_before: vec![],
        }
    }

    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
    }

    pub fn into_block(self) -> Block {
        Block::new(self.span, vec![self])
    }
}

impl StatementId {
    pub fn fresh() -> StatementId {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        StatementId::new(id)
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

    /// Combine the span information from a [Switch]
    pub fn combine_targets_span(&self) -> Span {
        match self {
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
}
