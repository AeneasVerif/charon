//! Trait elaboration: given a trait reference, we track which impl and/or local clauses caused it to be true.
#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

mod elaboration;
mod predicates;
mod utils;

pub use elaboration::*;
pub use predicates::*;
pub use utils::*;

use rustc_hir::def_id::DefId;
use rustc_middle::ty;

#[derive(Debug, Clone)]
pub enum DestructData<'tcx> {
    /// A drop that does nothing, e.g. for scalars and pointers.
    Noop,
    /// An implicit `Destruct` local clause, if the `resolve_destruct_bounds` option is `false`. If
    /// that option is `true`, we'll add `Destruct` bounds to every type param, and use that to
    /// resolve `Destruct` impls of generics. If it's `false`, we use this variant to indicate that
    /// the clause comes from a generic or associated type.
    Implicit,
    /// The `drop_in_place` is known and non-trivial.
    Glue {
        /// The type we're generating glue for.
        ty: ty::Ty<'tcx>,
    },
}

#[derive(Debug, Clone)]
pub enum BuiltinTraitData<'tcx> {
    /// A virtual `Destruct` implementation.
    /// `Destruct` is implemented automatically for all types. For our purposes, we chose to attach
    /// the information about `drop_in_place` to that trait. This data tells us what kind of
    /// `drop_in_place` the target type has.
    Destruct(DestructData<'tcx>),
    /// Some other builtin trait.
    Other,
}

#[derive(Debug, Clone)]
pub enum PathChunk<'tcx> {
    AssocItem {
        item: ty::AssocItem,
        /// The arguments provided to the item (for GATs). Includes trait args.
        generic_args: ty::GenericArgsRef<'tcx>,
        /// The implemented predicate.
        predicate: ty::PolyTraitRef<'tcx>,
        /// The index of this predicate in the list returned by `ItemPredicates::Implied`.
        index: usize,
    },
    Parent {
        /// The implemented predicate.
        predicate: ty::PolyTraitRef<'tcx>,
        /// The index of this predicate in the list returned by `ItemPredicates::Implied`.
        index: usize,
    },
}
pub type Path<'tcx> = Vec<PathChunk<'tcx>>;

#[derive(Debug, Clone)]
pub enum ImplExprAtom<'tcx> {
    /// A concrete `impl Trait for Type {}` item.
    Concrete {
        def_id: DefId,
        generics: ty::GenericArgsRef<'tcx>,
    },
    /// A context-bound clause like `where T: Trait`.
    LocalBound {
        predicate: ty::Predicate<'tcx>,
        id: ItemPredicateId,
        r#trait: ty::PolyTraitRef<'tcx>,
        path: Path<'tcx>,
    },
    /// The automatic clause `Self: Trait` present inside a `impl Trait for Type {}` item.
    SelfImpl {
        r#trait: ty::PolyTraitRef<'tcx>,
        path: Path<'tcx>,
    },
    /// `dyn Trait` is a wrapped value with a virtual table for trait
    /// `Trait`.  In other words, a value `dyn Trait` is a dependent
    /// triple that gathers a type τ, a value of type τ and an
    /// instance of type `Trait`.
    /// `dyn Trait` implements `Trait` using a built-in implementation; this refers to that
    /// built-in implementation.
    Dyn,
    /// A built-in trait whose implementation is computed by the compiler, such as `FnMut`. This
    /// morally points to an invisible `impl` block; as such it contains the information we may
    /// need from one.
    Builtin {
        /// Extra data for the given trait.
        trait_data: BuiltinTraitData<'tcx>,
        /// The `ImplExpr`s required to satisfy the implied predicates on the trait declaration.
        /// E.g. since `FnMut: FnOnce`, a built-in `T: FnMut` impl would have an `ImplExpr` for `T:
        /// FnOnce`.
        impl_exprs: Vec<ImplExpr<'tcx>>,
        /// The values of the associated types for this trait.
        types: Vec<(DefId, ty::Ty<'tcx>, Vec<ImplExpr<'tcx>>)>,
    },
    /// An error happened while elaborating traits.
    Error(String),
}

#[derive(Clone, Debug)]
pub struct ImplExpr<'tcx> {
    /// The trait this is an impl for.
    pub r#trait: ty::PolyTraitRef<'tcx>,
    /// The kind of implemention of the root of the tree.
    pub r#impl: ImplExprAtom<'tcx>,
}
