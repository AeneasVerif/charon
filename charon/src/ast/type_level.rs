use derive_generic_visitor::*;
use itertools::Itertools;
use serde_state::{DeserializeState, SerializeState};
use std::{collections::HashSet, mem};

use crate::ast::*;

pub mod regions;
pub mod substitute;
pub mod trait_proofs;
pub mod types;
pub mod vars;

pub use regions::*;
pub use substitute::*;
pub use trait_proofs::*;
pub use types::*;
pub use vars::*;

/// A set of generic arguments.
#[derive(
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct GenericArgs {
    pub regions: IndexVec<RegionId, Region>,
    pub types: IndexVec<TypeVarId, Ty>,
    pub const_generics: IndexVec<ConstGenericVarId, ConstantExpr>,
    pub trait_refs: IndexVec<TraitClauseId, TraitRef>,
}

/// A quantified trait predicate, e.g. `for<'a> Type<'a>: Trait<'a, Args>`.
pub type PolyTraitDeclRef = RegionBinder<TraitDeclRef>;

/// .0 outlives .1
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct OutlivesPred<T, U>(pub T, pub U);

pub type RegionOutlives = OutlivesPred<Region, Region>;
pub type TypeOutlives = OutlivesPred<Ty, Region>;

/// A constraint over a trait associated type.
///
/// Example:
/// ```text
/// T : Foo<S = String>
///         ^^^^^^^^^^
/// ```
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct TraitTypeConstraint {
    pub trait_ref: TraitRef,
    pub type_id: AssocTypeId,
    pub ty: Ty,
}

pub type BoxedArgs = Box<GenericArgs>;

/// Generic parameters for a declaration, including predicates.
#[derive(
    Default,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct GenericParams {
    #[serde_state(stateless)]
    pub regions: IndexVec<RegionId, RegionParam>,
    #[serde_state(stateless)]
    pub types: IndexVec<TypeVarId, TypeParam>,
    pub const_generics: IndexVec<ConstGenericVarId, ConstGenericParam>,
    // TODO: rename to match [GenericArgs]?
    pub trait_clauses: IndexVec<TraitClauseId, TraitParam>,
    /// The first region in the pair outlives the second region
    pub regions_outlive: Vec<RegionBinder<RegionOutlives>>,
    /// The type outlives the region
    pub types_outlive: Vec<RegionBinder<TypeOutlives>>,
    /// Constraints over trait associated types
    pub trait_type_constraints: IndexVec<TraitTypeConstraintId, RegionBinder<TraitTypeConstraint>>,
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("BK"))]
pub enum BinderKind {
    /// The parameters of a generic associated type.
    TraitType(TraitDeclId, AssocTypeId),
    /// The parameters of a trait method. Used in the `methods` lists in trait decls and trait
    /// impls.
    TraitMethod(TraitDeclId, TraitMethodId),
    /// The parameters bound in a non-trait `impl` block. Used in the `Name`s of inherent methods.
    InherentImplBlock,
    /// Binder used for `dyn Trait` existential predicates.
    Dyn,
    /// Some other use of a binder outside the main Charon ast.
    Other,
}

/// A value of type `T` bound by generic parameters. Used in any context where we're adding generic
/// parameters that aren't on the top-level item, e.g. `for<'a>` clauses (uses `RegionBinder` for
/// now), trait methods, GATs (TODO).
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct Binder<T> {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_params"))]
    pub params: GenericParams,
    /// Named this way to highlight accesses to the inner value that might be handling parameters
    /// incorrectly. Prefer using helper methods.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_value"))]
    pub skip_binder: T,
    /// The kind of binder this is.
    #[cfg_attr(feature = "charon_on_charon", charon::opaque)]
    pub kind: BinderKind,
}

/// A value of type `T` bound by regions. We should use `binder` instead but this causes name clash
/// issues in the derived ocaml visitors.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct RegionBinder<T> {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_regions"))]
    #[serde_state(stateless)]
    pub regions: IndexVec<RegionId, RegionParam>,
    /// Named this way to highlight accesses to the inner value that might be handling parameters
    /// incorrectly. Prefer using helper methods.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("binder_value"))]
    pub skip_binder: T,
}

impl GenericArgs {
    pub fn len(&self) -> usize {
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        regions.len() + types.len() + const_generics.len() + trait_refs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Whether this has any explicit arguments (types, regions or const generics).
    pub fn has_explicits(&self) -> bool {
        !self.regions.is_empty() || !self.types.is_empty() || !self.const_generics.is_empty()
    }
    /// Whether this has any implicit arguments (trait refs).
    pub fn has_implicits(&self) -> bool {
        !self.trait_refs.is_empty()
    }

    pub fn empty() -> Self {
        GenericArgs {
            regions: Default::default(),
            types: Default::default(),
            const_generics: Default::default(),
            trait_refs: Default::default(),
        }
    }

    pub fn new(
        regions: IndexVec<RegionId, Region>,
        types: IndexVec<TypeVarId, Ty>,
        const_generics: IndexVec<ConstGenericVarId, ConstantExpr>,
        trait_refs: IndexVec<TraitClauseId, TraitRef>,
    ) -> Self {
        Self {
            regions,
            types,
            const_generics,
            trait_refs,
        }
    }
    pub fn new_types(types: IndexVec<TypeVarId, Ty>) -> Self {
        Self {
            types,
            ..Self::empty()
        }
    }
    pub fn new_lifetimes(regions: IndexVec<RegionId, Region>) -> Self {
        Self {
            regions,
            ..Self::empty()
        }
    }

    /// Check whether this matches the given `GenericParams`.
    /// TODO: check more things, e.g. that the trait refs use the correct trait and generics.
    pub fn matches(&self, params: &GenericParams) -> bool {
        params.regions.len() == self.regions.len()
            && params.types.len() == self.types.len()
            && params.const_generics.len() == self.const_generics.len()
            && params.trait_clauses.len() == self.trait_refs.len()
    }

    /// Return the same generics, but where we pop the first type arguments.
    /// This is useful for trait references (for pretty printing for instance),
    /// because the first type argument is the type for which the trait is
    /// implemented.
    pub fn pop_first_type_arg(&self) -> (Ty, Self) {
        let mut generics = self.clone();
        let mut it = mem::take(&mut generics.types).into_iter();
        let ty = it.next().unwrap();
        generics.types = it.collect();
        (ty, generics)
    }

    /// Concatenate this set of arguments with another one. Use with care, you must manage the
    /// order of arguments correctly.
    pub fn concat(mut self, other: &Self) -> Self {
        let Self {
            regions,
            types,
            const_generics,
            trait_refs,
        } = other;
        self.regions.clone_extend_from_other(regions);
        self.types.clone_extend_from_other(types);
        self.const_generics.clone_extend_from_other(const_generics);
        self.trait_refs.clone_extend_from_other(trait_refs);
        self
    }
}

impl GenericParams {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Whether this has any explicit arguments (types, regions or const generics).
    pub fn has_explicits(&self) -> bool {
        !self.regions.is_empty() || !self.types.is_empty() || !self.const_generics.is_empty()
    }
    /// Whether this has any implicit arguments (trait clauses, outlives relations, associated type
    /// equality constraints).
    pub fn has_predicates(&self) -> bool {
        !self.trait_clauses.is_empty()
            || !self.types_outlive.is_empty()
            || !self.regions_outlive.is_empty()
            || !self.trait_type_constraints.is_empty()
    }

    /// Run some sanity checks.
    pub fn check_consistency(&self) {
        // Sanity check: check the clause ids are consistent.
        assert!(
            self.trait_clauses
                .iter()
                .enumerate()
                .all(|(i, c)| c.clause_id.index() == i)
        );

        // Sanity check: region names are pairwise distinct (this caused trouble when generating
        // names for the backward functions in Aeneas): at some point, Rustc introduced names equal
        // to `Some("'_")` for the anonymous regions, instead of using `None` (we now check in
        // [translate_region_name] and ignore names equal to "'_").
        let mut s = HashSet::new();
        for r in &self.regions {
            if let Some(name) = &r.name {
                assert!(
                    !s.contains(name),
                    "Name \"{}\" reused for two different lifetimes",
                    name
                );
                s.insert(name);
            }
        }
    }

    pub fn len(&self) -> usize {
        let GenericParams {
            regions,
            types,
            const_generics,
            trait_clauses,
            regions_outlive,
            types_outlive,
            trait_type_constraints,
        } = self;
        regions.len()
            + types.len()
            + const_generics.len()
            + trait_clauses.len()
            + regions_outlive.len()
            + types_outlive.len()
            + trait_type_constraints.len()
    }

    /// Construct a set of generic arguments in the scope of `self` that matches `self` and feeds
    /// each required parameter with itself. E.g. given parameters for `<T, U> where U:
    /// PartialEq<T>`, the arguments would be `<T, U>[TraitClause0]`.
    pub fn identity_args(&self) -> GenericArgs {
        self.identity_args_at_depth(DeBruijnId::zero())
    }

    /// Like `identity_args` but uses variables bound at the given depth.
    pub fn identity_args_at_depth(&self, depth: DeBruijnId) -> GenericArgs {
        GenericArgs {
            regions: self
                .regions
                .map_ref_indexed(|id, _| Region::Var(DeBruijnVar::bound(depth, id))),
            types: self
                .types
                .map_ref_indexed(|id, _| TyKind::TypeVar(DeBruijnVar::bound(depth, id)).into_ty()),
            const_generics: self.const_generics.map_ref_indexed(|id, c| ConstantExpr {
                ty: c.ty.clone(),
                kind: ConstantExprKind::Var(DeBruijnVar::bound(depth, id)),
            }),
            trait_refs: self
                .trait_clauses
                .map_ref(|clause| clause.identity_tref_at_depth(depth)),
        }
    }

    /// Take the predicates from the another `GenericParams`. This assumes the clause ids etc are
    /// already consistent.
    pub fn take_predicates_from(&mut self, other: GenericParams) {
        assert!(!other.has_explicits());
        let num_clauses = self.trait_clauses.len();
        let GenericParams {
            regions: _,
            types: _,
            const_generics: _,
            trait_clauses,
            regions_outlive,
            types_outlive,
            trait_type_constraints,
        } = other;
        self.trait_clauses
            .extend(trait_clauses.into_iter().update(|clause| {
                clause.clause_id += num_clauses;
            }));
        self.regions_outlive.extend(regions_outlive);
        self.types_outlive.extend(types_outlive);
        self.trait_type_constraints.extend(trait_type_constraints);
    }

    /// Take the predicates from the another `GenericParams`. This assumes that the two
    /// `GenericParams` are independent, hence will shift clause ids if `other` has any
    /// trait refs that reference its own clauses.
    pub fn merge_predicates_from(&mut self, mut other: GenericParams) {
        // Drop the explicits params.
        other.types.clear();
        other.regions.clear();
        other.const_generics.clear();
        // The contents of `other` may refer to its own trait clauses, so we must shift clause ids.
        struct ShiftClausesVisitor(usize);
        impl VarsVisitor for ShiftClausesVisitor {
            fn visit_clause_var(&mut self, v: ClauseDbVar) -> Option<TraitRefKind> {
                if let DeBruijnVar::Bound(DeBruijnId::ZERO, clause_id) = v {
                    // Replace clause 0 and decrement the others.
                    Some(TraitRefKind::Clause(DeBruijnVar::Bound(
                        DeBruijnId::ZERO,
                        clause_id + self.0,
                    )))
                } else {
                    None
                }
            }
        }
        let num_clauses = self.trait_clauses.len();
        other.visit_vars(&mut ShiftClausesVisitor(num_clauses));
        self.take_predicates_from(other);
    }
}

impl<T> Binder<T> {
    /// Wrap the value in an empty binder, shifting variables appropriately.
    pub fn empty(kind: BinderKind, x: T) -> Self
    where
        T: TyVisitable,
    {
        Binder {
            params: Default::default(),
            skip_binder: x.move_under_binder(),
            kind,
        }
    }
    pub fn new(kind: BinderKind, params: GenericParams, skip_binder: T) -> Self {
        Self {
            params,
            skip_binder,
            kind,
        }
    }

    /// Whether this binder binds any variables.
    pub fn binds_anything(&self) -> bool {
        !self.params.is_empty()
    }

    /// Retreive the contents of this binder if the binder binds no variables. This is the invers
    /// of `Binder::empty`.
    pub fn get_if_binds_nothing(&self) -> Option<T>
    where
        T: TyVisitable + Clone,
    {
        self.params
            .is_empty()
            .then(|| self.skip_binder.clone().move_from_under_binder().unwrap())
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Binder<U> {
        Binder {
            params: self.params,
            skip_binder: f(self.skip_binder),
            kind: self.kind,
        }
    }

    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> Binder<U> {
        Binder {
            params: self.params.clone(),
            skip_binder: f(&self.skip_binder),
            kind: self.kind.clone(),
        }
    }

    /// Substitute the provided arguments for the variables bound in this binder and return the
    /// substituted inner value.
    pub fn apply(self, args: &GenericArgs) -> T
    where
        T: TyVisitable,
    {
        self.skip_binder.substitute(args)
    }
}

impl<T: AstVisitable> Binder<Binder<T>> {
    /// Flatten two levels of binders into a single one.
    pub fn flatten(self) -> Binder<T> {
        #[derive(Visitor)]
        struct FlattenVisitor<'a> {
            shift_by: &'a GenericParams,
            binder_depth: DeBruijnId,
        }
        impl VisitorWithBinderDepth for FlattenVisitor<'_> {
            fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
                &mut self.binder_depth
            }
        }
        impl VisitAstMut for FlattenVisitor<'_> {
            fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ControlFlow<Self::Break> {
                VisitWithBinderDepth::new(self).visit(x)
            }

            fn enter_de_bruijn_id(&mut self, db_id: &mut DeBruijnId) {
                if *db_id > self.binder_depth {
                    // We started visiting at the inner binder, so in this branch we're either
                    // mentioning the outer binder or a binder further beyond. Either way we
                    // decrease the depth; variables that point to the outer binder don't have to
                    // be shifted.
                    *db_id = db_id.decr();
                }
            }
            fn enter_region(&mut self, x: &mut Region) {
                if let Region::Var(var) = x
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.regions.len();
                }
            }
            fn enter_ty_kind(&mut self, x: &mut TyKind) {
                if let TyKind::TypeVar(var) = x
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.types.len();
                }
            }
            fn enter_constant_expr(&mut self, x: &mut ConstantExpr) {
                if let ConstantExprKind::Var(ref mut var) = x.kind
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.const_generics.len();
                }
            }
            fn enter_trait_ref_kind(&mut self, x: &mut TraitRefKind) {
                if let TraitRefKind::Clause(var) = x
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.trait_clauses.len();
                }
            }
        }

        // We will concatenate both sets of params.
        let mut outer_params = self.params;

        // The inner value needs to change:
        // - at binder level 0 we shift all variable ids to match the concatenated params;
        // - at binder level > 0 we decrease binding level because there's one fewer binder.
        let mut bound_value = self.skip_binder.skip_binder;
        let _ = bound_value.drive_mut(&mut FlattenVisitor {
            shift_by: &outer_params,
            binder_depth: Default::default(),
        });

        // The inner params must also be updated, as they can refer to themselves and the outer
        // one.
        let mut inner_params = self.skip_binder.params;
        let _ = inner_params.drive_mut(&mut FlattenVisitor {
            shift_by: &outer_params,
            binder_depth: Default::default(),
        });
        inner_params
            .regions
            .iter_mut()
            .for_each(|v| v.index += outer_params.regions.len());
        inner_params
            .types
            .iter_mut()
            .for_each(|v| v.index += outer_params.types.len());
        inner_params
            .const_generics
            .iter_mut()
            .for_each(|v| v.index += outer_params.const_generics.len());
        inner_params
            .trait_clauses
            .iter_mut()
            .for_each(|v| v.clause_id += outer_params.trait_clauses.len());

        let GenericParams {
            regions,
            types,
            const_generics,
            trait_clauses,
            regions_outlive,
            types_outlive,
            trait_type_constraints,
        } = &inner_params;
        outer_params.regions.clone_extend_from_other(regions);
        outer_params.types.clone_extend_from_other(types);
        outer_params
            .const_generics
            .clone_extend_from_other(const_generics);
        outer_params
            .trait_clauses
            .clone_extend_from_other(trait_clauses);
        outer_params
            .regions_outlive
            .extend_from_slice(regions_outlive);
        outer_params.types_outlive.extend_from_slice(types_outlive);
        outer_params
            .trait_type_constraints
            .clone_extend_from_other(trait_type_constraints);

        Binder {
            params: outer_params,
            skip_binder: bound_value,
            kind: BinderKind::Other,
        }
    }
}

impl<T> RegionBinder<T> {
    /// Wrap the value in an empty region binder, shifting variables appropriately.
    pub fn empty(x: T) -> Self
    where
        T: TyVisitable,
    {
        RegionBinder {
            regions: Default::default(),
            skip_binder: x.move_under_binder(),
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> RegionBinder<U> {
        RegionBinder {
            regions: self.regions,
            skip_binder: f(self.skip_binder),
        }
    }

    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> RegionBinder<U> {
        RegionBinder {
            regions: self.regions.clone(),
            skip_binder: f(&self.skip_binder),
        }
    }

    /// Substitute the bound variables with the given lifetimes.
    pub fn apply(self, regions: IndexVec<RegionId, Region>) -> T
    where
        T: TyVisitable,
    {
        assert_eq!(regions.len(), self.regions.len());
        let args = GenericArgs {
            regions,
            ..GenericArgs::empty()
        };
        self.skip_binder.substitute_inner_binder(&args)
    }

    /// Substitute the bound variables with erased lifetimes.
    pub fn erase(self) -> T
    where
        T: TyVisitable,
    {
        let regions = self.regions.map_ref_indexed(|_, _| Region::Erased);
        self.apply(regions)
    }
}

pub trait HasIdxVecOf<Id: Idx>: std::ops::Index<Id, Output: Sized> {
    fn get_idx_vec(&self) -> &IndexVec<Id, Self::Output>;
    fn get_idx_vec_mut(&mut self) -> &mut IndexVec<Id, Self::Output>;
}

/// Delegate `Index` implementations to subfields.
macro_rules! mk_index_impls {
    ($ty:ident.$field:ident[$idx:ty]: $output:ty) => {
        impl std::ops::Index<$idx> for $ty {
            type Output = $output;
            fn index(&self, index: $idx) -> &Self::Output {
                &self.$field[index]
            }
        }
        impl std::ops::IndexMut<$idx> for $ty {
            fn index_mut(&mut self, index: $idx) -> &mut Self::Output {
                &mut self.$field[index]
            }
        }
        impl HasIdxVecOf<$idx> for $ty {
            fn get_idx_vec(&self) -> &IndexVec<$idx, Self::Output> {
                &self.$field
            }
            fn get_idx_vec_mut(&mut self) -> &mut IndexVec<$idx, Self::Output> {
                &mut self.$field
            }
        }
    };
}
mk_index_impls!(GenericArgs.regions[RegionId]: Region);
mk_index_impls!(GenericArgs.types[TypeVarId]: Ty);
mk_index_impls!(GenericArgs.const_generics[ConstGenericVarId]: ConstantExpr);
mk_index_impls!(GenericArgs.trait_refs[TraitClauseId]: TraitRef);
mk_index_impls!(GenericParams.regions[RegionId]: RegionParam);
mk_index_impls!(GenericParams.types[TypeVarId]: TypeParam);
mk_index_impls!(GenericParams.const_generics[ConstGenericVarId]: ConstGenericParam);
mk_index_impls!(GenericParams.trait_clauses[TraitClauseId]: TraitParam);
