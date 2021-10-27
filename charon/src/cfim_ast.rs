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
use crate::vars::Name;
use hashlink::linked_hash_map::LinkedHashMap;
use im::{OrdMap, OrdSet, Vector};
use macros::{EnumAsGetters, EnumIsA, VariantName};
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct Assert {
    pub cond: Operand,
    pub expected: bool,
}

#[derive(Debug, Clone)]
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
    Statement(Statement),
    Sequence(Box<Expression>, Box<Expression>),
    Switch(Operand, SwitchTargets),
    Loop(Box<Expression>),
}

pub type FunDecls = DefId::Vector<FunDecl>;

/// A function declaration
#[derive(Debug, Clone)]
pub struct FunDecl {
    pub def_id: DefId::Id,
    pub name: Name,
    /// The signature contains the inputs/output types *with* non-erased regions.
    /// It also contains the list of region and type parameters.
    pub signature: FunSig,
    /// true if the function might diverge (is recursive, part of a mutually
    /// recursive group, contains loops or calls functions which might diverge)
    pub divergent: bool,
    pub arg_count: usize,
    pub locals: VarId::Vector<Var>,
    pub body: Expression,
}
