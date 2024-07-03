//! "Unstructured LLBC" ast (ULLBC). This is LLBC before the control-flow
//! reconstruction. In effect, this is a cleaned up version of MIR.
pub use super::ullbc_ast_utils::*;
pub use crate::ast::*;
use crate::ids::Vector;
use derive_visitor::{Drive, DriveMut};
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};

// Block identifier. Similar to rust's `BasicBlock`.
generate_index_type!(BlockId, "Block");

// The entry block of a function is always the block with id 0
pub static START_BLOCK_ID: BlockId = BlockId::ZERO;

pub type BodyContents = Vector<BlockId, BlockData>;
pub type ExprBody = GExprBody<BodyContents>;

/// A raw statement: a statement without meta data.
#[derive(
    Debug, Clone, EnumIsA, EnumAsGetters, VariantName, Serialize, Deserialize, Drive, DriveMut,
)]
pub enum RawStatement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId),
    /// We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC
    StorageDead(VarId),
    /// We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC
    Deinit(Place),
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
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(BlockId, BlockId),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    SwitchInt(IntegerTy, Vec<(ScalarValue, BlockId)>, BlockId),
}

/// A raw terminator: a terminator without meta data.
#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize, Deserialize, Drive, DriveMut)]
pub enum RawTerminator {
    Goto {
        target: BlockId,
    },
    Switch {
        discr: Operand,
        targets: SwitchTargets,
    },
    /// Handles panics and impossible cases.
    Abort(AbortKind),
    Return,
    Drop {
        place: Place,
        target: BlockId,
    },
    /// Function call. If `target` is `None`, the function is guaranteed to diverge.
    /// For now, we don't support dynamic calls (i.e. to a function pointer in memory).
    Call {
        call: Call,
        target: Option<BlockId>,
    },
    /// A built-in assert, which corresponds to runtime checks that we remove, namely: bounds
    /// checks, over/underflow checks, div/rem by zero checks, pointer alignement check.
    Assert {
        cond: Operand,
        expected: bool,
        target: BlockId,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct Terminator {
    pub span: Span,
    pub content: RawTerminator,
}

#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct BlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}
