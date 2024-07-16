//! LLBC
//!
//! MIR code where we have rebuilt the control-flow (`if ... then ... else ...`,
//! `while ...`, ...).
//!
//! Also note that we completely break the definitions Statement and Terminator
//! from MIR to use Statement only.

pub use super::llbc_ast_utils::*;
pub use crate::ast::*;
use derive_visitor::{Drive, DriveMut};
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};

/// Asserts are special constructs introduced by Rust to perform dynamic
/// checks, to detect out-of-bounds accesses or divisions by zero for
/// instance. We eliminate the assertions in [crate::remove_dynamic_checks],
/// then introduce other dynamic checks in [crate::reconstruct_asserts].
#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct Assert {
    pub cond: Operand,
    pub expected: bool,
}

/// A raw statement: a statement without meta data.
#[derive(
    Debug, Clone, EnumIsA, EnumToGetters, EnumAsGetters, Serialize, Deserialize, Drive, DriveMut,
)]
pub enum RawStatement {
    /// Assigns an `Rvalue` to a `Place`. e.g. `let y = x;` could become
    /// `y := move x` which is represented as `Assign(y, Rvalue::Use(Operand::Move(x)))`.
    Assign(Place, Rvalue),
    /// Only used for borrow-checking
    FakeRead(Place),
    /// Not used today because we take MIR built.
    SetDiscriminant(Place, VariantId),
    Drop(Place),
    Assert(Assert),
    Call(Call),
    /// Panic also handles "unreachable". We keep the name of the panicking function that was
    /// called.
    Abort(AbortKind),
    Return,
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
    /// The contained statements must NOT be sequences. To ensure that, use [Sequence::then] to
    /// build sequences.
    /// Note that on the ml side, sequences will be in the shape of
    /// `Sequence of statement * statement` where the second `statement` might
    ///  be a sequence if needed, but not the first one, e.g. `Sequence [a, b,
    ///  c]` becomes `Sequence (a, Sequence (b, c))`
    Sequence(Vec<Statement>),
    Switch(Switch),
    Loop(Box<Statement>),
    Error(String),
}

#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct Statement {
    pub span: Span,
    pub content: RawStatement,
}

#[derive(
    Debug,
    Clone,
    EnumIsA,
    EnumToGetters,
    EnumAsGetters,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    VariantName,
    VariantIndexArity,
)]
pub enum Switch {
    /// Gives the `if` block and the `else` block. The `Operand` is the condition of the `if`, e.g. `if (y == 0)` could become
    /// ```
    /// v@3 := copy y; // Represented as `Assign(v@3, Use(Copy(y))`
    /// v@2 := move v@3 == 0; // Represented as `Assign(v@2, BinOp(BinOp::Eq, Move(y), Const(0)))`
    /// if (move v@2) { // Represented as `If(Move(v@2), <then branch>, <else branch>)`
    /// ```
    If(Operand, Box<Statement>, Box<Statement>),
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
    SwitchInt(
        Operand,
        IntegerTy,
        Vec<(Vec<ScalarValue>, Statement)>,
        Box<Statement>,
    ),
    /// A match over an ADT.
    ///
    /// The match statement is introduced in [crate::remove_read_discriminant]
    /// (whenever we find a discriminant read, we merge it with the subsequent
    /// switch into a match).
    Match(
        Place,
        Vec<(Vec<VariantId>, Statement)>,
        Option<Box<Statement>>,
    ),
}

pub type BodyContents = Statement;
pub type ExprBody = GExprBody<BodyContents>;
