use crate::hax::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantInt {
    Int(i128, IntTy),
    Uint(u128, UintTy),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantLiteral {
    Bool(bool),
    Char(char),
    Float(String, u128, FloatTy),
    Int(ConstantInt),
    PtrNoProvenance(u128),
    Str(String),
    ByteStr(Vec<u8>),
}

sinto_reexport!(rustc_abi::VariantIdx);

/// Describe the kind of a variant
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VariantKind {
    Struct,
    Union,
    Enum { index: VariantIdx },
}

/// The subset of expressions that corresponds to constants.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantExprKind {
    Literal(ConstantLiteral),
    // Adts (structs, enums, unions) or closures.
    Adt {
        kind: VariantKind,
        fields: Vec<ConstantFieldExpr>,
    },
    Array {
        fields: Vec<ConstantExpr>,
    },
    Tuple {
        fields: Vec<ConstantExpr>,
    },
    /// A top-level or associated constant.
    ///
    /// Remark: constants *can* have generic parameters.
    /// Example:
    /// ```text
    /// struct V<const N: usize, T> {
    ///   x: [T; N],
    /// }
    ///
    /// impl<const N: usize, T> V<N, T> {
    ///   const LEN: usize = N; // This has generics <N, T>
    /// }
    ///
    /// impl Foo for Bar {
    ///   const C : usize = 32; // <-
    /// }
    /// ```
    ///
    /// If `options.inline_anon_consts` is `false`, this is also used for inline const blocks and
    /// advanced const generics expressions.
    NamedGlobal(ItemRef),
    /// A reference or raw pointer (as given by the type of this constant) to a place inside a
    /// constant value: `projections` applied to `base`, each with the type of the place it
    /// reaches.
    Ptr {
        base: ConstantPtrBase,
        projections: Vec<(ConstantProjectionElem, Ty)>,
        metadata: Option<UnsizingMetadata>,
    },
    /// Casts a thin pointer to the type of this constant. If metadata is given, this is an
    /// unsizing cast from the pointee of the given pointer.
    PtrCast(ConstantExpr, Option<UnsizingMetadata>),
    ConstRef {
        id: ParamConst,
    },
    /// A function definition, corresponding to a particular item. This is a ZST, unlike `FnPtr`.
    FnDef(ItemRef),
    /// A function pointer. This is an actual pointer to that function.
    FnPtr(FnPtrTarget),
    /// A blob of memory containing the byte representation of the value. This can occur when
    /// evaluating MIR constants (e.g. unions). Interpreting this back to a structured value
    /// is left as an exercice to the consumer.
    Memory(Vec<ConstantByte>),
    Todo(String),
}

/// The place a constant pointer starts from.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantPtrBase {
    /// The allocation behind this provenance, of the given type.
    Global(ConstantByteProvenance, Ty),
    /// A constant value that isn't stored in an allocation we name.
    Value(ConstantExpr),
}

/// Projects a place inside the pointee of a constant pointer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantProjectionElem {
    /// A field of a struct, tuple or closure, or of the given variant of an enum.
    Field(Option<VariantIdx>, FieldIdx),
    /// An element of an array.
    Index(u64),
    /// The subarray `array[from..to]`.
    Subslice { from: u64, to: u64 },
    /// The place `count * size_of(ty)` bytes after the current place, or
    /// `count` bytes if `ty` is `None`. If `in_bounds` is `false`, this may point outside of the
    /// allocation. `pointee_is_sized` proves that the resulting place is sized.
    Offset {
        count: i64,
        ty: Option<Ty>,
        in_bounds: bool,
        pointee_is_sized: TraitProof,
    },
}

/// A byte of an evaluated constant, in the MiniRust sense.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantByte {
    /// An uninitialized byte (e.g. padding, or the bytes of a union not covered by the active
    /// field).
    Uninit,
    /// A concrete byte value.
    Value(u8),
    /// A byte that is part of a pointer with provenance. The `u8` is the offset of this byte
    /// within the pointer.
    Provenance(ConstantByteProvenance, u8),
}

/// The function a function pointer points to.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FnPtrTarget {
    /// The function of an item.
    Fn(ItemRef),
    /// A stateless closure coerced to a function pointer.
    ClosureAsFn(ClosureArgs),
}

/// What a pointer byte in an evaluated constant points to.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantByteProvenance {
    /// A pointer to a static.
    Global(ItemRef),
    /// A pointer to a function, with the type of function pointers to it.
    Function(FnPtrTarget, Ty),
    /// A pointer to anything else (an anonymous allocation, a vtable...).
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstantFieldExpr {
    pub field: DefId,
    pub value: ConstantExpr,
}

/// Rustc has different representation for constants: one for MIR
/// ([`rustc_middle::mir::Const`]), one for the type system
/// ([`rustc_middle::ty::ConstKind`]). For simplicity hax maps those
/// two construct to one same `ConstantExpr` type.
pub type ConstantExpr = Decorated<ConstantExprKind>;

pub use self::uneval::*;
pub use rustc_const_uneval::{ConstSource, GlobalRef, ReadMode};
mod uneval;
