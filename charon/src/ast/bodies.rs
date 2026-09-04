//! The bodies of functions.
use crate::ast::*;
use crate::ids::IndexVec;
use crate::llbc_ast;
use crate::ullbc_ast;
use crate::utils::serialize_map_to_array::SeqHashMapToArray;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::EnumAsGetters;
use macros::{EnumIsA, EnumToGetters};
use serde_state::DeserializeState;
use serde_state::SerializeState;

pub mod expressions;
pub mod places;
pub mod structured;
pub mod unstructured;
pub mod values;

pub use expressions::*;
pub use places::*;
pub use values::*;

/// The body of a function.
#[derive(
    Debug,
    Clone,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
)]
#[serde_state(state_implements = DedupSerializerState)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Body"))]
pub enum Body {
    /// Body represented as a CFG. This is what ullbc is made of, and what we get after translating MIR.
    Unstructured(ullbc_ast::ExprBody),
    /// Body represented with structured control flow. This is what llbc is made of. We restructure
    /// the control flow in the `ullbc_to_llbc` pass.
    Structured(llbc_ast::ExprBody),
    /// A façade body that dispatches to one of several per-target function bodies. Created during
    /// multi-target merging for functions with the same signature but different bodies across
    /// targets.
    TargetDispatch(
        #[serde(with = "SeqHashMapToArray::<TargetTriple, FunDeclRef>")]
        SeqHashMap<TargetTriple, FunDeclRef>,
    ),
    /// Function declared in an `extern { ... }` block. The string is the foreign symbol name.
    Extern(String),
    /// Rust intrinsic function.
    Intrinsic {
        /// The intrinsic name.
        name: String,
        /// The argument names, None if not available.
        arg_names: Vec<Option<String>>,
    },
    /// A body that the user chose not to translate, based on opacity settings like
    /// `--include`/`--opaque`.
    Opaque,
    /// A body that was not available. Typically that's function bodies for non-generic and
    /// non-inlineable std functions, as these are not present in the compiled standard library
    /// `.rmeta` file shipped with a rust toolchain.
    Missing,
    /// We encountered an error while translating this body.
    #[serde_state(stateless)]
    Error(Error),
}

generate_index_type!(LocalId, "");

/// The local variables of a body.
#[derive(Debug, Default, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct Locals {
    /// The number of local variables used for the input arguments.
    pub arg_count: usize,
    /// The local variables.
    /// We always have, in the following order:
    /// - the local used for the return value (index 0)
    /// - the `arg_count` input arguments
    /// - the remaining locals, used for the intermediate computations
    pub locals: IndexVec<LocalId, Local>,
}

/// A variable
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct Local {
    /// Unique index identifying the variable
    pub index: LocalId,
    /// Variable name - may be `None` if the variable was introduced by Rust
    /// through desugaring.
    pub name: Option<String>,
    /// Span of the variable declaration.
    pub span: Span,
    /// The variable type
    #[cfg_attr(feature = "charon_on_charon", charon::rename("local_ty"))]
    pub ty: Ty,
}

/// An expression body.
/// TODO: arg_count should be stored in GFunDecl below. But then,
///       the print is obfuscated and Aeneas may need some refactoring.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("GexprBody"))]
pub struct GExprBody<T> {
    pub span: Span,
    /// The number of regions existentially bound in this body. We introduce fresh such regions
    /// during translation instead of the erased regions that rustc gives us.
    pub bound_body_regions: usize,
    /// The local variables.
    pub locals: Locals,
    /// The statements and blocks that compose this body.
    pub body: T,
    /// For each line inside the body, we record any whole-line `//` comments found before it. They
    /// are added to statements in the late `recover_body_comments` pass.
    #[cfg_attr(feature = "charon_on_charon", charon::opaque)]
    pub comments: Vec<(u32, Vec<String>)>,
}

generate_index_type!(BranchId, "Branch");

/// The value inspected by a switch. Must be of integer, bool or char type.
#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Switch"))]
pub enum SwitchScrutinee {
    /// Inspect the value produced by an operand.
    Value(Operand),
    /// Inspect the discriminant of an enum place.
    Discriminant(Place),
}

/// A branching operation.
#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
pub struct SwitchData {
    /// The value to branch over.
    pub scrutinee: SwitchScrutinee,
    /// Which branch to take for each value of the scrutinee. Several values may point to the same
    /// branch, and not all values may be accounted for.
    ///
    /// If the scrutinee is an operand, the constant expressions are literal values. If the
    /// scrutinee is a discriminant read, the expressions are of the form
    /// `ConstantExprKind::Discriminant`.
    pub branches: Vec<(ConstantExpr, BranchId)>,
    /// Branch to use if the scrutinee didn't match any of the values above. `None` if the set of
    /// branch values is known to be exhaustive.
    pub fallback: Option<BranchId>,
}

/// A function operand is used in function calls.
/// It either designates a top-level function, or a place in case
/// we are using function pointers stored in local variables.
#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("FnOp"))]
pub enum FnOperand {
    /// Regular case: call to a top-level function, trait method, etc.
    Regular(FnPtr),
    /// Use of a function pointer.
    Dynamic(Operand),
}

#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
pub struct Call {
    pub func: FnOperand,
    pub args: Vec<Operand>,
    pub dest: Place,
}

/// Statements that only affect borrow-checking. They are no-ops at runtime.
#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
pub enum BorrowckStatement {
    /// Acts like a read of the place.
    FakeRead(Place),
    /// Relate the type of a place to the provided type. For example, `let x: Self = value`
    /// produces `SetType` for `x` and `Self`.
    SetType {
        place: Place,
        ty: Ty,
        #[serde_state(stateless)]
        variance: Variance,
    },
    /// Require a type to outlive a region. For example, the `'a` bound in
    /// `let x: impl Copy + 'a = value` produces `SetOutlives(typeof(x), 'a)`.
    SetOutlives(Ty, Region),
    /// Require a trait predicate to hold. For example, the `Copy` bound in
    /// `let x: impl Copy = value` produces `PredicateHolds(typeof(x): Copy)`.
    PredicateHolds(TraitRef),
}

/// (U)LLBC is a language with side-effects: a statement may abort in a way that isn't tracked by
/// control-flow. The three kinds of abort are:
/// - Panic
/// - Undefined behavior (caused by an "assume")
/// - Unwind termination
#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
pub enum AbortKind {
    /// A built-in panicking function, or a panic due to a failed built-in check (e.g. for out-of-bounds accesses).
    Panic(Option<Name>),
    /// Undefined behavior in the rust abstract machine.
    UndefinedBehavior,
    /// Unwind had to stop for ABI reasons or because cleanup code panicked again.
    UnwindTerminate,
}

/// A `Drop` statement/terminator can mean two things, depending on what MIR phase we retrieved
/// from rustc: it could be a real drop, or it could be a "conditional drop", which is where drop
/// may happen depending on whether the borrow-checker determines a drop is needed.
#[derive(
    Debug, PartialEq, Eq, Clone, Copy, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
pub enum DropKind {
    /// A real drop. This calls `<T as Destruct>::drop_glue(&mut place)` and marks the
    /// place as moved-out-of. Use `--desugar-drops` to transform all such drops to an actual
    /// function call.
    ///
    /// The `drop_glue` method is added by Charon to the `Destruct` trait to make it possible
    /// to track drop code in polymorphic code. It contains the same code as the
    /// `core::ptr::drop_glue<T>` builtin would.
    ///
    /// Drop are precise in MIR `elaborated` and `optimized`.
    Precise,
    /// A conditional drop, which may or may not end up running drop code depending on the code
    /// path that led to it. A conditional drop may also become a partial drop (dropping only the
    /// subplaces that haven't been moved out of), may be conditional on the code path that led to
    /// it, or become an async drop. The exact semantics are left intentionally unspecified by
    /// rustc developers. To elaborate such drops into precise drops, pass `--precise-drops` to
    /// Charon.
    ///
    /// A conditional drop may also be passed an unaligned place when dropping fields of packed
    /// structs. Such a thing is UB for a precise drop.
    ///
    /// Drop are conditional in MIR `built` and `promoted`.
    Conditional,
}

/// Check the value of an operand and abort if the value is not expected. This is introduced to
/// avoid a lot of small branches.
///
/// We translate MIR asserts (introduced for out-of-bounds accesses or divisions by zero for
/// instance) to this. We then eliminate them in [crate::transform::resugar::reconstruct_fallible_operations],
/// because they're implicit in the semantics of our array accesses etc. Finally we introduce new asserts in
/// [crate::transform::resugar::reconstruct_asserts].
#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("Assertion"))]
pub struct Assert {
    pub cond: Operand,
    /// The value that the operand should evaluate to for the assert to succeed.
    pub expected: bool,
    /// The kind of check performed by this assert. This is only used for error reporting, as the check
    /// is actually performed by the instructions preceding the assert.
    pub check_kind: Option<BuiltinAssertKind>,
}

/// The kind of a built-in assertion, which may panic and unwind. These are removed
/// by `reconstruct_fallible_operations` because they're implicit in the semantics of (U)LLBC.
/// This kind should only be used for error-reporting purposes, as the check itself
/// is performed in the instructions preceding the assert.
#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
pub enum BuiltinAssertKind {
    BoundsCheck { len: Operand, index: Operand },
    Overflow(BinOp, Operand, Operand),
    OverflowNeg(Operand),
    DivisionByZero(Operand),
    RemainderByZero(Operand),
    MisalignedPointerDereference { required: Operand, found: Operand },
    NullPointerDereference,
    NullReferenceCreated,
    InvalidEnumConstruction(Operand),
    ResumedAfterReturn,
    ResumedAfterPanic,
    ResumedAfterDrop,
}

impl Body {
    /// Whether there is an actual body with statements etc, as opposed to the body being missing
    /// for some reason.
    pub fn has_contents(&self) -> bool {
        match self {
            Body::Unstructured(..) | Body::Structured(..) => true,
            Body::Extern(..)
            | Body::Intrinsic { .. }
            | Body::Opaque
            | Body::Missing
            | Body::Error(..)
            | Body::TargetDispatch(..) => false,
        }
    }

    pub fn locals(&self) -> &Locals {
        match self {
            Body::Structured(body) => &body.locals,
            Body::Unstructured(body) => &body.locals,
            _ => panic!("called `locals` on a missing body"),
        }
    }
}

impl Locals {
    pub fn new(arg_count: usize) -> Self {
        Self {
            arg_count,
            locals: Default::default(),
        }
    }

    /// Creates a new variable and returns a place pointing to it.
    /// Warning: don't forget to `StorageLive` it before using it.
    pub fn new_var(&mut self, name: Option<String>, ty: Ty) -> Place {
        let local_id = self.locals.push_with(|index| Local {
            index,
            name,
            span: Span::dummy(),
            ty: ty.clone(),
        });
        Place::new(local_id, ty)
    }

    /// Gets a place pointing to the corresponding variable.
    pub fn place_for_var(&self, local_id: LocalId) -> Place {
        let ty = self.locals[local_id].ty.clone();
        Place::new(local_id, ty)
    }

    /// Returns whether this local is the special return local or one of the input argument locals.
    pub fn is_return_or_arg(&self, lid: LocalId) -> bool {
        lid.index() <= self.arg_count
    }

    /// The place where we write the return value.
    pub fn return_place(&self) -> Place {
        self.place_for_var(LocalId::new(0))
    }

    /// Locals that aren't arguments or return values.
    pub fn non_argument_locals(&self) -> impl Iterator<Item = (LocalId, &Local)> {
        self.locals.iter_enumerated().skip(1 + self.arg_count)
    }
}

impl SwitchData {
    /// If this is a switch over a boolean, return its `then` and `else` branches.
    pub fn as_if(&self) -> Option<(BranchId, BranchId)> {
        let SwitchScrutinee::Value(scrutinee) = &self.scrutinee else {
            return None;
        };
        if !matches!(scrutinee.ty().kind(), TyKind::Literal(LiteralTy::Bool)) {
            return None;
        }

        let branch_for = |value| {
            self.branches
                .iter()
                .find_map(|(case, branch_id)| match case.kind() {
                    ConstantExprKind::Literal(Literal::Bool(case_value))
                        if *case_value == value =>
                    {
                        Some(*branch_id)
                    }
                    _ => None,
                })
                .or(self.fallback)
        };
        Some((branch_for(true)?, branch_for(false)?))
    }

    /// Group the explicit switch values by the branch they select.
    pub fn group_by_branch(&self) -> IndexVec<BranchId, Vec<ConstantExpr>> {
        let mut grouped = IndexVec::new();
        if let Some(branch_id) = self.fallback {
            grouped.get_or_extend_and_insert(branch_id, Vec::new);
        }
        for (value, branch_id) in &self.branches {
            grouped
                .get_or_extend_and_insert(*branch_id, Vec::new)
                .push(value.clone());
        }
        grouped
    }
}

impl std::ops::Index<LocalId> for Locals {
    type Output = Local;
    fn index(&self, local_id: LocalId) -> &Self::Output {
        &self.locals[local_id]
    }
}
impl std::ops::IndexMut<LocalId> for Locals {
    fn index_mut(&mut self, local_id: LocalId) -> &mut Self::Output {
        &mut self.locals[local_id]
    }
}
