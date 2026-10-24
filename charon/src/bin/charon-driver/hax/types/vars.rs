use crate::hax::prelude::*;
use crate::hax::sinto_as_usize;

use macros::{EnumAsGetters, EnumIsA};
use rustc_middle::ty;

/// Reflects [`ty::ParamTy`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ParamTy, state: S as gstate)]
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`ty::ParamConst`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<S>, from: ty::ParamConst, state: S as gstate)]
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`ty::BoundTyKind`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundTyKind<'tcx>, state: S as s)]
pub enum BoundTyKind {
    Anon,
    #[custom_arm(&FROM_TYPE::Param(def_id) => TO_TYPE::Param(def_id.sinto(s), s.base().tcx.item_name(def_id).sinto(s)),)]
    Param(DefId, Symbol),
}

/// Reflects [`ty::BoundTy`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundTy<'tcx>, state: S as s)]
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoundTyRef {
    pub index: BoundVarIndexKind,
    pub ty: BoundTy,
}

sinto_as_usize!(rustc_middle::ty, BoundVar);

/// Reflects [`ty::BoundRegionKind`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundRegionKind<'tcx>, state: S as s)]
pub enum BoundRegionKind {
    Anon,
    NamedForPrinting(Symbol),
    #[custom_arm(&FROM_TYPE::Named(def_id) => TO_TYPE::Named(def_id.sinto(s), s.base().tcx.item_name(def_id).sinto(s)),)]
    Named(DefId, Symbol),
    ClosureEnv,
}

/// Reflects [`ty::BoundRegion`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundRegion<'tcx>, state: S as s)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

/// Reflects [`ty::PlaceholderRegion`]
pub type PlaceholderRegion = Placeholder<BoundRegion>;
/// Reflects [`ty::PlaceholderConst`]
pub type PlaceholderConst = Placeholder<BoundVar>;
/// Reflects [`ty::PlaceholderType`]
pub type PlaceholderTy = Placeholder<BoundTy>;

/// Reflects [`ty::Placeholder`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Placeholder<T> {
    pub bound: T,
}

impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Placeholder<U>>
    for ty::Placeholder<ty::TyCtxt<'tcx>, T>
{
    fn sinto(&self, s: &S) -> Placeholder<U> {
        Placeholder {
            bound: self.bound.sinto(s),
        }
    }
}

/// Reflects [`rustc_middle::infer::canonical::Canonical`]
#[derive(Debug, Clone)]
pub struct Canonical<T> {
    pub value: T,
}
/// Reflects [`ty::CanonicalUserType`]
pub type CanonicalUserType = Canonical<UserType>;

impl<'tcx, S: UnderOwnerState<'tcx>, T: SInto<S, U>, U> SInto<S, Canonical<U>>
    for rustc_middle::infer::canonical::Canonical<'tcx, T>
{
    fn sinto(&self, s: &S) -> Canonical<U> {
        Canonical {
            value: self.value.sinto(s),
        }
    }
}

/// Reflects [`ty::EarlyParamRegion`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::EarlyParamRegion, state: S as s)]
pub struct EarlyParamRegion {
    pub index: u32,
    pub name: Symbol,
}

/// Reflects [`ty::LateParamRegion`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::LateParamRegion<'tcx>, state: S as s)]
pub struct LateParamRegion {
    pub scope: DefId,
    pub kind: LateParamRegionKind,
}

/// Reflects [`ty::LateParamRegionKind`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::LateParamRegionKind, state: S as s)]
pub enum LateParamRegionKind {
    Anon(u32),
    NamedAnon(u32, Symbol),
    #[custom_arm(&FROM_TYPE::Named(def_id) => TO_TYPE::Named(def_id.sinto(s), s.base().tcx.item_name(def_id).sinto(s)),)]
    Named(DefId, Symbol),
    ClosureEnv,
}

/// Reflects [`ty::RegionKind`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::RegionKind<'tcx>, state: S as gstate)]
pub enum RegionKind {
    ReEarlyParam(EarlyParamRegion),
    ReBound(BoundVarIndexKind, BoundRegion),
    ReLateParam(LateParamRegion),
    ReStatic,
    ReVar(RegionVid),
    RePlaceholder(PlaceholderRegion),
    ReErased,
    ReError(ErrorGuaranteed),
}

/// Reflects [`ty::BoundVarIndexKind`]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundVarIndexKind, state: S as gstate)]
pub enum BoundVarIndexKind {
    Bound(DebruijnIndex),
    Canonical,
}

sinto_as_usize!(rustc_middle::ty, DebruijnIndex);
sinto_as_usize!(rustc_middle::ty, RegionVid);

/// Reflects [`ty::Region`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::Region<'tcx>, state: S as s)]
pub struct Region {
    #[value(self.kind().sinto(s))]
    pub kind: RegionKind,
}

/// Reflects both [`ty::GenericArg`] and [`ty::GenericArgKind`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(EnumIsA, EnumAsGetters)]
#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::GenericArgKind<'tcx>, state: S as s)]
pub enum GenericArg<'tcx> {
    Lifetime(Region),
    Type(Ty<'tcx>),
    Const(ConstantExpr<'tcx>),
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, GenericArg<'tcx>> for ty::GenericArg<'tcx> {
    fn sinto(&self, s: &S) -> GenericArg<'tcx> {
        self.kind().sinto(s)
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Vec<GenericArg<'tcx>>> for ty::GenericArgsRef<'tcx> {
    fn sinto(&self, s: &S) -> Vec<GenericArg<'tcx>> {
        self.iter().map(|v| v.kind().sinto(s)).collect()
    }
}

/// Reflects partially [`ty::InferTy`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S>, from: ty::InferTy, state: S as gstate)]
pub enum InferTy {
    #[custom_arm(FROM_TYPE::TyVar(..) => TO_TYPE::TyVar,)]
    TyVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::IntVar(..) => TO_TYPE::IntVar,)]
    IntVar, /*TODO?*/
    #[custom_arm(FROM_TYPE::FloatVar(..) => TO_TYPE::FloatVar,)]
    FloatVar, /*TODO?*/
    FreshTy(u32),
    FreshIntTy(u32),
    FreshFloatTy(u32),
}

/// Reflects [`ty::Variance`]
#[derive(AdtInto)]
#[args(<S>, from: ty::Variance, state: S as _s)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Variance {
    Covariant,
    Invariant,
    Contravariant,
    Bivariant,
}

/// Reflects [`ty::GenericParamDef`]
#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::GenericParamDef, state: S as s)]
#[derive(Debug, Clone)]
pub struct GenericParamDef<'tcx> {
    pub name: Symbol,
    pub def_id: DefId,
    pub index: u32,
    pub pure_wrt_drop: bool,
    #[value(
        match self.kind {
            ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
            ty::GenericParamDefKind::Type { has_default, synthetic } => GenericParamDefKind::Type { has_default, synthetic },
            ty::GenericParamDefKind::Const { has_default, .. } => {
                let tcx = s.base().tcx;
                let ty = if let Some(item) = s.owner().as_synthetic(s)
                    && let Some(ty) = item.const_param_ty(s, self.index)
                {
                    // We use a dummy `DefId` for the generic params of synthetic items, so
                    // `tcx.type_of` would be wrong.
                    ty::Unnormalized::new(ty)
                } else {
                    tcx.type_of(self.def_id).instantiate_identity()
                };
                let ty = normalize(tcx, s.typing_env(), ty).sinto(s);
                GenericParamDefKind::Const { has_default, ty }
            },
        }
    )]
    pub kind: GenericParamDefKind<'tcx>,
    /// Variance of this type parameter, if sensible.
    #[value({
        use SyntheticItem::*;
        use rustc_hir::def::DefKind::*;
        let tcx = s.base().tcx;
        match s.owner().as_synthetic(s) {
            Some(Array | Slice | Tuple(_) | Str) => Some(Variance::Covariant),
            // We could compute it but we won't need it since this item is only used in impls.
            Some(FnPtr(_)) => None,
            None => {
                let parent = tcx.parent(self.def_id);
                match tcx.def_kind(parent) {
                    Fn | AssocFn | Enum | Struct | Union | Ctor(..) | OpaqueTy => {
                        tcx.variances_of(parent).get(self.index as usize).sinto(s)
                    }
                    _ => None,
                }
            }
        }
    })]
    pub variance: Option<Variance>,
}

/// Reflects [`ty::GenericParamDefKind`]
#[derive(Debug, Clone)]
pub enum GenericParamDefKind<'tcx> {
    Lifetime,
    Type { has_default: bool, synthetic: bool },
    Const { has_default: bool, ty: Ty<'tcx> },
}

/// Reflects [`ty::Generics`]
#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::Generics, state: S as state)]
#[derive(Debug, Clone)]
pub struct TyGenerics<'tcx> {
    pub parent: Option<DefId>,
    pub parent_count: usize,
    #[from(own_params)]
    pub params: Vec<GenericParamDef<'tcx>>,
    // pub param_def_id_to_index: FxHashMap<DefId, u32>,
    pub has_self: bool,
    pub has_late_bound_regions: Option<Span>,
}

pub type UnitBinder<'tcx> = ty::Binder<'tcx, ()>;

/// Reflects [`ty::BoundVariableKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::BoundVariableKind<'tcx>, state: S as tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoundVariableKind {
    Ty(BoundTyKind),
    #[custom_arm(
        &FROM_TYPE::Region(region) => TO_TYPE::Region(region.sinto(tcx), None),
    )]
    Region(BoundRegionKind, Option<Variance>),
    Const,
}

/// Reflects [`ty::Binder`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Binder<T> {
    pub value: T,
    pub bound_vars: Vec<BoundVariableKind>,
}

impl Binder<()> {
    pub fn empty() -> Self {
        Binder {
            value: (),
            bound_vars: vec![],
        }
    }
}

impl<T> Binder<T> {
    pub fn as_ref(&self) -> Binder<&T> {
        Binder {
            value: &self.value,
            bound_vars: self.bound_vars.clone(),
        }
    }

    pub fn hax_skip_binder(self) -> T {
        self.value
    }

    pub fn hax_skip_binder_ref(&self) -> &T {
        &self.value
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Binder<U> {
        Binder {
            value: f(self.value),
            bound_vars: self.bound_vars,
        }
    }

    pub fn inner_mut(&mut self) -> &mut T {
        &mut self.value
    }

    pub fn rebind<U>(&self, value: U) -> Binder<U> {
        self.as_ref().map(|_| value)
    }
}

/// A representation of `exists<T: Trait1 + Trait2>(value)`: we create a fresh type id and the
/// appropriate trait clauses. The contained value may refer to the fresh ty and the in-scope trait
/// clauses. This is used to represent types related to `dyn Trait`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DynBinder<'tcx, T> {
    /// Fresh type parameter that we use as the `Self` type in the predicates below.
    pub existential_ty: ParamTy,
    /// Clauses that define the trait object. These clauses use the fresh type parameter above
    /// as `Self` type.
    pub predicates: GenericPredicates<'tcx>,
    /// The value inside the binder.
    pub val: T,
}

impl<'tcx, S, T, U> SInto<S, DynBinder<'tcx, U>>
    for rustc_trait_elaboration::DynBinder<'tcx, T, DefId>
where
    S: UnderOwnerState<'tcx>,
    T: SInto<S, U>,
{
    fn sinto(&self, s: &S) -> DynBinder<'tcx, U> {
        DynBinder {
            existential_ty: self.existential_ty.sinto(s),
            predicates: GenericPredicates {
                predicates: self.predicates.sinto(s),
            },
            val: self.val.sinto(s),
        }
    }
}

/// Lets types declare how to compute the variance of bound parameters.
trait BinderVariances<'tcx>: Sized {
    fn variances(
        _tcx: ty::TyCtxt<'tcx>,
        _binder: &ty::Binder<'tcx, Self>,
    ) -> HashMap<ty::BoundVar, ty::Variance> {
        HashMap::default()
    }
}

impl<'tcx> BinderVariances<'tcx> for ty::FnSig<'tcx> {
    fn variances(
        tcx: ty::TyCtxt<'tcx>,
        binder: &ty::Binder<'tcx, Self>,
    ) -> HashMap<ty::BoundVar, ty::Variance> {
        fn_sig_bound_region_variances(tcx, *binder)
    }
}

impl<'tcx> BinderVariances<'tcx> for ty::Ty<'tcx> {}
impl<'tcx> BinderVariances<'tcx> for ty::ClauseKind<'tcx> {}
impl<'tcx> BinderVariances<'tcx> for ty::PredicateKind<'tcx> {}
impl<'tcx> BinderVariances<'tcx> for ty::TraitRef<'tcx> {}
impl<'tcx> BinderVariances<'tcx> for ty::TraitClause<'tcx> {}

impl<'tcx, S: UnderOwnerState<'tcx>, T1, T2> SInto<S, Binder<T2>> for ty::Binder<'tcx, T1>
where
    T1: SInto<(StateWithOwner<'tcx>, UnitBinder<'tcx>), T2> + BinderVariances<'tcx>,
{
    fn sinto(&self, s: &S) -> Binder<T2> {
        let variances = T1::variances(s.base().tcx, self);
        let mut bound_vars = self.bound_vars().sinto(s);
        for (index, var) in bound_vars.iter_mut().enumerate() {
            if let BoundVariableKind::Region(_, variance) = var {
                *variance = variances
                    .get(&ty::BoundVar::from_usize(index))
                    .copied()
                    .sinto(s);
            }
        }
        let value = {
            // Keep the binder in the context, for when we translate predicates and such. This
            // erases a preexisting binder in context, which is fine because we only need it
            // immediately.
            let under_binder_s = (s.as_state_with_owner(), self.as_ref().map_bound(|_| ()));
            self.as_ref().skip_binder().sinto(&under_binder_s)
        };
        Binder { value, bound_vars }
    }
}
