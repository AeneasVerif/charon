//! Our Internal MIR ast (IM), intended to be close to the rust compiler MIR ast.
//! We don't even try to reconstruct the if then else blocks or the loop blocks
//! at this point.
#![allow(dead_code)]

use crate::expressions::*;
pub use crate::im_ast_utils::*;
use crate::regions_hierarchy::RegionGroups;
use crate::types::*;
use crate::values::*;
use crate::vars::Name;
use hashlink::linked_hash_map::LinkedHashMap;
use macros::generate_index_type;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::Serialize;

// TODO: move this definition
pub static TAB_INCR: &'static str = "    ";

generate_index_type!(FunDefId);

// Block identifier. Similar to rust's `BasicBlock`.
generate_index_type!(BlockId);

pub static START_BLOCK_ID: BlockId::Id = BlockId::ZERO;

/// A variable
#[derive(Debug, Clone, Serialize)]
pub struct Var {
    /// Unique index identifying the variable
    pub index: VarId::Id,
    /// Variable name - may be `None` if the variable was introduced by Rust
    /// through desugaring.
    pub name: Option<String>,
    /// The variable type
    pub ty: ETy,
}

/// A function signature.
/// Note that a signature uses unerased lifetimes, while function bodies (and
/// execution) use erased lifetimes.
/// We need the functions' signatures *with* the region parameters in order
/// to correctly abstract those functions (number and signature of the backward
/// functions) - we only use regions for this purpose.
#[derive(Debug, Clone, Serialize)]
pub struct FunSig {
    pub region_params: RegionVarId::Vector<RegionVar>,
    /// The region parameters contain early bound and late bound parameters.
    /// The early bound regions are those introduced by the `impl` block (if
    /// this definition  is defined in an `impl` block), the late bound regions
    /// are those introduced by the function itself.
    ///  For example, in:
    ///  ```
    ///  impl<'a> Foo<'a> {
    ///      fn bar<'b>(...) -> ... { ... }
    ///  }
    /// `'a` is early-bound while `'b` is late-bound.
    ///  ```
    pub num_early_bound_regions: usize,
    /// The lifetime's hierarchy between the different regions.
    pub regions_hierarchy: RegionGroups,
    pub type_params: TypeVarId::Vector<TypeVar>,
    pub inputs: VarId::Vector<RTy>,
    pub output: RTy,
}

/// A function definition
#[derive(Debug, Clone, Serialize)]
pub struct GFunDef<T: std::fmt::Debug + Clone + Serialize> {
    pub def_id: FunDefId::Id,
    pub name: Name,
    /// The signature contains the inputs/output types *with* non-erased regions.
    /// It also contains the list of region and type parameters.
    pub signature: FunSig,
    pub arg_count: usize,
    pub locals: VarId::Vector<Var>,
    pub body: T,
}

pub type FunDef = GFunDef<BlockId::Vector<BlockData>>;

pub type FunDefs = FunDefId::Vector<FunDef>;

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, Serialize)]
pub enum Statement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId::Id),
    StorageDead(VarId::Id),
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(BlockId::Id, BlockId::Id),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    /// Also, we use a `LinkedHashMap` to make sure the order of the switch
    /// branches is preserved.
    SwitchInt(
        IntegerTy,
        LinkedHashMap<ScalarValue, BlockId::Id>,
        BlockId::Id,
    ),
}

/// A function identifier. See [`Terminator`](Terminator)
#[derive(Debug, Clone, Copy, EnumIsA, EnumAsGetters, VariantName, Serialize)]
pub enum FunId {
    /// A function local to the crate, whose body we will translate.
    Local(FunDefId::Id),
    /// An assumed function, coming from a standard library (for instance:
    /// `alloc::boxed::Box::new`).
    Assumed(AssumedFunId),
}

/// An assumed function identifier, identifying a function coming from a
/// standard library.
#[derive(Debug, Clone, Copy, EnumIsA, EnumAsGetters, Serialize)]
pub enum AssumedFunId {
    /// `core::mem::replace`
    Replace,
    /// `alloc::boxed::Box::new`
    BoxNew,
    /// `core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref`
    BoxDeref,
    /// `core::ops::deref::DerefMut::<alloc::boxed::Box<T>>::deref_mut`
    BoxDerefMut,
    /// `alloc::alloc::box_free`
    /// This is actually an unsafe function, but the rust compiler sometimes
    /// introduces it when going to MIR. We add it only to track it: in practice,
    /// its semantic is given by a "drop".
    BoxFree,
    /// `alloc::vec::Vec::new`
    VecNew,
    /// `alloc::vec::Vec::push`
    VecPush,
    /// `alloc::vec::Vec::insert`
    VecInsert,
    /// `alloc::vec::Vec::len`
    VecLen,
    /// `core::ops::index::Index::index<alloc::vec::Vec<T>, usize>`
    VecIndex,
    /// `core::ops::index::IndexMut::index_mut<alloc::vec::Vec<T>, usize>`
    VecIndexMut,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum Terminator {
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
        func: FunId,
        /// Technically, this is useless, but we still keep it because we might
        /// want to introduce some information (and the way we encode from MIR
        /// is as simple as possible - and in MIR we also have a vector of erased
        /// regions).
        region_params: Vec<ErasedRegion>,
        type_params: Vec<ETy>,
        args: Vec<Operand>,
        dest: Place,
        target: BlockId::Id,
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: BlockId::Id,
    },
}

#[derive(Debug, Clone, Serialize)]
pub struct BlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}
