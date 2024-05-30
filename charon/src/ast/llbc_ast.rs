//! LLBC
//!
//! MIR code where we have rebuilt the control-flow (`if ... then ... else ...`,
//! `while ...`, ...).
//!
//! Also note that we completely break the definitions Statement and Terminator
//! from MIR to use Statement only.

pub use crate::gast::*;
use crate::ids::Map;
pub use crate::llbc_ast_utils::*;
use crate::meta::Span;
use crate::types::*;
pub use crate::ullbc_ast::{Call, FunDeclId, GlobalDeclId, Var};
use crate::values::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};

/// Asserts are special constructs introduced by Rust to perform dynamic
/// checks, to detect out-of-bounds accesses or divisions by zero for
/// instance. We eliminate the assertions in [crate::remove_dynamic_checks],
/// then introduce other dynamic checks in [crate::reconstruct_asserts].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Assert {
    pub cond: Operand,
    pub expected: bool,
}

/// A raw statement: a statement without meta data.
#[derive(Debug, Clone, EnumIsA, EnumToGetters, EnumAsGetters, Serialize, Deserialize)]
pub enum RawStatement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId),
    Drop(Place),
    Assert(Assert),
    Call(Call),
    /// Panic also handles "unreachable"
    Panic,
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
    /// The left statement must NOT be a sequence.
    /// For instance, `(s0; s1); s2` is forbidden and should be rewritten
    /// to the semantically equivalent statement `s0; (s1; s2)`
    /// To ensure that, use [crate::llbc_ast_utils::new_sequence] to build sequences.
    Sequence(Box<Statement>, Box<Statement>),
    Switch(Switch),
    Loop(Box<Statement>),
    Error(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
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
    VariantName,
    VariantIndexArity,
)]
pub enum Switch {
    /// Gives the `if` block and the `else` block
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

pub type ExprBody = GExprBody<Statement>;

pub type FunDecl = GFunDecl<Statement>;
pub type FunDecls = Map<FunDeclId, FunDecl>;

pub type GlobalDecl = GGlobalDecl<Statement>;
pub type GlobalDecls = Map<GlobalDeclId, GlobalDecl>;
