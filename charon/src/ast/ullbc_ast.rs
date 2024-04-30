//! "Unstructured LLBC" ast (ULLBC). This is LLBC before the control-flow
//! reconstruction. In effect, this is a cleaned up version of MIR.
pub use crate::gast::*;
use crate::meta::Meta;
pub use crate::types::GlobalDeclId;
use crate::types::*;
pub use crate::ullbc_ast_utils::*;
use crate::values::*;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::Serialize;

// Block identifier. Similar to rust's `BasicBlock`.
generate_index_type!(BlockId);

// The entry block of a function is always the block with id 0
pub static START_BLOCK_ID: BlockId::Id = BlockId::ZERO;

pub type ExprBody = GExprBody<BlockId::Vector<BlockData>>;

pub type FunDecl = GFunDecl<BlockId::Vector<BlockData>>;
pub type FunDecls = FunDeclId::Map<FunDecl>;

pub type GlobalDecl = GGlobalDecl<BlockId::Vector<BlockData>>;
pub type GlobalDecls = GlobalDeclId::Map<GlobalDecl>;

pub type TraitDecls = TraitDeclId::Map<TraitDecl>;
pub type TraitImpls = TraitImplId::Map<TraitImpl>;

/// A raw statement: a statement without meta data.
#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, Serialize)]
pub enum RawStatement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId::Id),
    /// We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC
    StorageDead(VarId::Id),
    /// We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC
    Deinit(Place),
}

#[derive(Debug, Clone, Serialize)]
pub struct Statement {
    pub meta: Meta,
    pub content: RawStatement,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity, Serialize)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(BlockId::Id, BlockId::Id),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    SwitchInt(IntegerTy, Vec<(ScalarValue, BlockId::Id)>, BlockId::Id),
}

/// A raw terminator: a terminator without meta data.
#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum RawTerminator {
    Goto {
        target: BlockId::Id,
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
        target: BlockId::Id,
    },
    /// Function call.
    /// For now, we only accept calls to top-level functions.
    Call {
        call: Call,
        target: BlockId::Id,
    },
    /// A built-in assert, which corresponds to runtime checks that we remove, namely: bounds
    /// checks, over/underflow checks, div/rem by zero checks, pointer alignement check.
    Assert {
        cond: Operand,
        expected: bool,
        target: BlockId::Id,
    },
}

#[derive(Debug, Clone, Serialize)]
pub struct Terminator {
    pub meta: Meta,
    pub content: RawTerminator,
}

#[derive(Debug, Clone, Serialize)]
pub struct BlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}
