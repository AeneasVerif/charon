use crate::hax::prelude::*;
use crate::hax::sinto_todo;

use rustc_middle::ty;

/// A predicate without `Self`, for use in `dyn Trait`.
///
/// Reflects [`ty::ExistentialPredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ExistentialPredicate<'tcx>, state: S as state)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExistentialPredicate {
    /// E.g. `From<u64>`. Note that this isn't `T: From<u64>` with a given `T`, this is just
    /// `From<u64>`. Could be written `?: From<u64>`.
    Trait(ExistentialTraitRef),
    /// E.g. `Iterator::Item = u64`. Could be written `<? as Iterator>::Item = u64`.
    Projection(ExistentialProjection),
    /// E.g. `Send`.
    AutoTrait(DefId),
}

/// Reflects [`ty::ExistentialTraitRef`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ExistentialTraitRef<'tcx>, state: S as state)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExistentialTraitRef {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
}

/// Reflects [`ty::ExistentialProjection`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ExistentialProjection<'tcx>, state: S as state)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExistentialProjection {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
    pub term: Term,
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GenericPredicate>
    for rustc_trait_elaboration::DynPredicate<'tcx, DefId>
{
    fn sinto(&self, s: &S) -> GenericPredicate {
        let tcx = s.base().tcx;
        let pred = &self.predicate;
        if let Some(projection) = pred.clause.as_projection_clause() {
            let trait_proof = self
                .projection_trait_proof
                .expect("projection predicates should have a trait proof")
                .sinto(s);
            let bound_vars = projection.bound_vars().sinto(s);
            let projection = projection.skip_binder();
            let alias_ty = projection.projection_term.expect_ty();
            let Term::Ty(ty) = projection.term.sinto(s) else {
                unreachable!()
            };
            let item = tcx.associated_item(alias_ty_kind_def_id(alias_ty.kind));
            GenericPredicate {
                id: pred.id.sinto(s),
                clause: Clause {
                    kind: Binder {
                        value: ClauseKind::Projection(ProjectionPredicate {
                            trait_proof,
                            assoc_item: AssocItem::sfrom(s, &item),
                            ty,
                        }),
                        bound_vars,
                    },
                },
                span: pred.span.sinto(s),
            }
        } else {
            assert!(self.projection_trait_proof.is_none());
            pred.sinto(s)
        }
    }
}

pub(super) fn resolve_for_dyn<'tcx, S, T, U>(
    s: &S,
    epreds: &'tcx ty::List<ty::Binder<'tcx, ty::ExistentialPredicate<'tcx>>>,
    f: impl FnOnce(&mut PredicateSearcher<'tcx>, ty::Ty<'tcx>) -> T,
) -> DynBinder<U>
where
    S: UnderOwnerState<'tcx>,
    T: SInto<S, U>,
{
    s.with_predicate_searcher(|searcher, state| searcher.resolve_for_dyn(state, epreds, f))
        .sinto(s)
}

/// Reflects [`ty::TraitClause`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::TraitClause<'tcx>, state: S as tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
    #[map(*x == ty::ClausePolarity::Positive)]
    #[from(polarity)]
    pub is_positive: bool,
}

/// Reflects [`ty::OutlivesPredicate`] as a named struct
/// instead of a tuple struct. This is because the script converting
/// JSONSchema types to OCaml doesn't support tuple structs, and this
/// is the only tuple struct in the whole AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OutlivesPredicate<T> {
    pub lhs: T,
    pub rhs: Region,
}

impl<'tcx, S: UnderOwnerState<'tcx>, T, U> SInto<S, OutlivesPredicate<U>>
    for ty::OutlivesClause<'tcx, T>
where
    T: SInto<S, U>,
{
    fn sinto(&self, s: &S) -> OutlivesPredicate<U> where {
        OutlivesPredicate {
            lhs: self.0.sinto(s),
            rhs: self.1.sinto(s),
        }
    }
}

/// Reflects [`ty::RegionOutlivesPredicate`]
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;
/// Reflects [`ty::TypeOutlivesPredicate`]
pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;

/// Reflects [`ty::Term`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Ty(Ty),
    Const(ConstantExpr),
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Term> for ty::Term<'tcx> {
    fn sinto(&self, s: &S) -> Term {
        use ty::TermKind;
        match self.kind() {
            TermKind::Ty(ty) => Term::Ty(ty.sinto(s)),
            TermKind::Const(c) => Term::Const(c.sinto(s)),
        }
    }
}

/// Expresses a constraints over an associated type.
///
/// For instance:
/// ```text
/// fn f<T : Foo<S = String>>(...)
///              ^^^^^^^^^^
/// ```
/// (provided the trait `Foo` has an associated type `S`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProjectionPredicate {
    /// The `impl Trait for Ty` in `Ty: Trait<..., Type = U>`.
    pub trait_proof: TraitProof,
    /// The `Type` in `Ty: Trait<..., Type = U>`.
    pub assoc_item: AssocItem,
    /// The type `U` in `Ty: Trait<..., Type = U>`.
    pub ty: Ty,
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<(S, UnitBinder<'tcx>), ProjectionPredicate>
    for ty::ProjectionClause<'tcx>
{
    fn sinto(&self, s: &(S, UnitBinder<'tcx>)) -> ProjectionPredicate {
        let tcx = s.base().tcx;
        let alias_ty = &self.projection_term.expect_ty();
        let poly_trait_ref = s.1.rebind(alias_ty.trait_ref(tcx));
        let Term::Ty(ty) = self.term.sinto(s) else {
            unreachable!()
        };
        let item = tcx.associated_item(alias_ty_kind_def_id(alias_ty.kind));
        ProjectionPredicate {
            trait_proof: solve_trait(s, poly_trait_ref),
            assoc_item: AssocItem::sfrom(s, &item),
            ty,
        }
    }
}

/// Reflects [`ty::ClauseKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ClauseKind<'tcx>, state: (S, UnitBinder<'tcx>) as tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClauseKind {
    Trait(TraitPredicate),
    RegionOutlives(RegionOutlivesPredicate),
    TypeOutlives(TypeOutlivesPredicate),
    Projection(ProjectionPredicate),
    ConstArgHasType(ConstantExpr, Ty),
    WellFormed(Term),
    ConstEvaluatable(ConstantExpr),
    HostEffect(HostEffectClause),
    UnstableFeature(Symbol),
}

sinto_todo!(rustc_middle::ty, HostEffectClause<'tcx>);

/// Reflects [`ty::Clause`] and adds a hash-consed predicate identifier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Clause {
    pub kind: Binder<ClauseKind>,
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Clause> for ty::Clause<'tcx> {
    fn sinto(&self, s: &S) -> Clause {
        let kind = self.kind().sinto(s);
        Clause { kind }
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Clause> for ty::PolyTraitClause<'tcx> {
    fn sinto(&self, s: &S) -> Clause {
        let kind: Binder<_> = self.sinto(s);
        let kind: Binder<ClauseKind> = kind.map(ClauseKind::Trait);
        Clause { kind }
    }
}

/// Reflects [`ty::Predicate`] and adds a hash-consed predicate identifier.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub kind: Binder<PredicateKind>,
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Predicate> for ty::Predicate<'tcx> {
    fn sinto(&self, s: &S) -> Predicate {
        let kind = self.kind().sinto(s);
        Predicate { kind }
    }
}

/// Uniquely identifies a predicate.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: traits::ItemPredicateId<DefId>, state: S as s)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericPredicateId {
    /// A predicate that counts as "input" for an item, e.g. `where` clauses on a function or impl.
    /// Numbered in some arbitrary but consistent order.
    Required(DefId, u32),
    /// A predicate that counts as "output" of an item, e.g. supertrait clauses in a trait. Note
    /// that we count `where` clauses on a trait as implied.
    /// Numbered in some arbitrary but consistent order.
    Implied(DefId, u32),
    /// Predicate inside a non-item binder, e.g. within a `dyn Trait`.
    /// Numbered in some arbitrary but consistent order.
    Unmapped(u32),
    /// The special `Self: Trait` clause available within trait `Trait`.
    TraitSelf,
}

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: traits::ItemPredicate<'tcx, DefId>, state: S as s)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericPredicate {
    pub id: GenericPredicateId,
    pub clause: Clause,
    pub span: Span,
}

/// Reflects [`ty::GenericPredicates`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: traits::ItemPredicates<'tcx, DefId>, state: S as s)]
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct GenericPredicates {
    pub predicates: Vec<GenericPredicate>,
}

impl GenericPredicates {
    pub fn iter(&self) -> impl Iterator<Item = &GenericPredicate> {
        self.predicates.iter()
    }
    /// Iter only on trait clauses.
    pub fn iter_trait_clauses(&self) -> impl Iterator<Item = &GenericPredicate> {
        self.iter()
            .filter(|pred| matches!(pred.clause.kind.hax_skip_binder_ref(), ClauseKind::Trait(_)))
    }
}

/// Reflects [`ty::SubtypePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::SubtypePredicate<'tcx>, state: S as tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SubtypePredicate {
    pub a_is_expected: bool,
    pub a: Ty,
    pub b: Ty,
}

/// Reflects [`ty::CoercePredicate`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::CoercePredicate<'tcx>, state: S as tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CoercePredicate {
    pub a: Ty,
    pub b: Ty,
}

sinto_todo!(rustc_middle::ty, NormalizesTo<'tcx>);

/// Reflects [`ty::PredicateKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::PredicateKind<'tcx>, state: (S, UnitBinder<'tcx>) as tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PredicateKind {
    Clause(ClauseKind),
    DynCompatible(DefId),
    Subtype(SubtypePredicate),
    Coerce(CoercePredicate),
    ConstEquate(ConstantExpr, ConstantExpr),
    Ambiguous,
    NormalizesTo(NormalizesTo),
}
