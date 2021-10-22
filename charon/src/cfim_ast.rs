//! CFIM: Control-Flow Internal MIR
//!
//! MIR code where we have rebuilt the control-flow (`if ... then ... else ...`,
//! `while ...`, ...).
//!
//! Also note that we completely break the definitions Statement and Terminator
//! from MIR to use Statement and Expression. The Statement definition in this
//! file doesn't correspond at all to the Statement definition from MIR.

#![allow(dead_code)]
use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::im_ast::*;
use crate::types::*;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use im::{OrdMap, OrdSet, Vector};
use macros::{EnumAsGetters, EnumIsA, VariantName};
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct Assert {
    cond: Operand,
    expected: bool,
    target: BlockId::Id,
}

#[derive(Debug, Clone)]
pub struct Call {
    func: FunId,
    /// Technically this is useless, but we still keep it because we might
    /// want to introduce some information (and the way we encode from MIR
    /// is as simple as possible - and in MIR we also have a vector of erased
    /// regions).
    region_params: Vec<ErasedRegion>,
    type_params: Vec<ETy>,
    args: Vec<Operand>,
    dest: Place,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters)]
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
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(Box<Expression>, Box<Expression>),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    /// Also, we use a `LinkedHashMap` to make sure the order of the switch
    /// branches is preserved.
    SwitchInt(
        IntegerTy,
        LinkedHashMap<ScalarValue, Expression>,
        Box<Expression>,
    ),
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters)]
pub enum Expression {
    Sequence(Statement, Box<Expression>),
    Switch(Operand, SwitchTargets),
}
