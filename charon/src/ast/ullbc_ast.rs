//! "Unstructured LLBC" ast (ULLBC). This is LLBC before the control-flow
//! reconstruction. In effect, this is a cleaned up version of MIR.
pub use crate::gast::*;
use crate::ids::{Map, Vector};
use crate::meta::Span;
pub use crate::types::GlobalDeclId;
use crate::types::*;
pub use crate::ullbc_ast_utils::*;
use crate::values::*;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};

// Block identifier. Similar to rust's `BasicBlock`.
generate_index_type!(BlockId, "Block");

// The entry block of a function is always the block with id 0
pub static START_BLOCK_ID: BlockId = BlockId::ZERO;

pub type ExprBody = GExprBody<Vector<BlockId, BlockData>>;

pub type FunDecl = GFunDecl<Vector<BlockId, BlockData>>;
pub type FunDecls = Map<FunDeclId, FunDecl>;

pub type GlobalDecl = GGlobalDecl<Vector<BlockId, BlockData>>;
pub type GlobalDecls = Map<GlobalDeclId, GlobalDecl>;

pub type TraitDecls = Map<TraitDeclId, TraitDecl>;
pub type TraitImpls = Map<TraitImplId, TraitImpl>;

/// A raw statement: a statement without meta data.
#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, Serialize, Deserialize)]
pub enum RawStatement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId),
    /// We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC
    StorageDead(VarId),
    /// We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC
    Deinit(Place),
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Statement {
    pub span: Span,
    pub content: RawStatement,
}

#[derive(
    Debug, Clone, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity, Serialize, Deserialize,
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
#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize, Deserialize)]
pub enum RawTerminator {
    Goto {
        target: BlockId,
    },
    Switch {
        discr: Operand,
        targets: SwitchTargets,
    },
    Panic,
    Return,
    Unreachable,
    Drop {
        place: Place,
        target: BlockId,
    },
    /// Function call.
    /// For now, we only accept calls to top-level functions.
    Call {
        call: Call,
        target: BlockId,
    },
    /// A built-in assert, which corresponds to runtime checks that we remove, namely: bounds
    /// checks, over/underflow checks, div/rem by zero checks, pointer alignement check.
    Assert {
        cond: Operand,
        expected: bool,
        target: BlockId,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Terminator {
    pub span: Span,
    pub content: RawTerminator,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}
