//! CFIM: Control-Flow Internal MIR
//!
//! MIR code where we have rebuilt the control-flow (`if ... then ... else ...`,
//! `while ...`, ...).
//!
//! Also note that we completely break the definitions Statement and Terminator
//! from MIR to use Statement only.

#![allow(dead_code)]
pub use crate::cfim_ast_utils::*;
use crate::expressions::*;
use crate::im_ast::*;
use crate::types::*;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct Assert {
    pub cond: Operand,
    pub expected: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct Call {
    pub func: FunId,
    /// Technically this is useless, but we still keep it because we might
    /// want to introduce some information (and the way we encode from MIR
    /// is as simple as possible - and in MIR we also have a vector of erased
    /// regions).
    pub region_params: Vec<ErasedRegion>,
    pub type_params: Vec<ETy>,
    pub args: Vec<Operand>,
    pub dest: Place,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum Statement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId::Id),
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
    Sequence(Box<Statement>, Box<Statement>),
    Switch(Operand, SwitchTargets),
    Loop(Box<Statement>),
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(Box<Statement>, Box<Statement>),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    /// Also, we use a `LinkedHashMap` to make sure the order of the switch
    /// branches is preserved.
    SwitchInt(
        IntegerTy,
        LinkedHashMap<ScalarValue, Statement>,
        Box<Statement>,
    ),
}

pub type FunDefs = FunDefId::Vector<FunDef>;

/// A function definition
pub type FunDef = GFunDef<Statement>;
