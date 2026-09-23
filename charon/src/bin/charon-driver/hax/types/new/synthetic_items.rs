use crate::hax::prelude::*;
use crate::translate::resolve_path::def_path_def_ids;
use charon_lib::name_matcher::NamePattern;

use itertools::Itertools;
use {
    rustc_attr_ir::LangItem,
    rustc_middle::ty,
    rustc_span::{DUMMY_SP, Symbol},
    rustc_type_ir::{TypeFoldable, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable, Upcast},
};

/// We create some extra `DefId`s to represent things that rustc doesn't have a `DefId` for. This
/// makes the pipeline much easier to have "real" def_ids for them, as we can then solve traits
/// for them etc, and works well with monomorphization.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum SyntheticItem {
    /// Fake ADT representing the `[T; N]` type.
    Array,
    /// Fake ADT representing the `[T]` type.
    Slice,
    /// Fake ADT representing the length-n tuple `(A, B, ...)`.
    Tuple(usize),
    /// Fake ADT representing `str`, which wraps a `[u8]`.
    Str,
    /// Fake item representing a particular shape of function pointer types.
    /// E.g. `for<'a> fn(&'a u32) -> Adt<'a, u32>` is considered to be an instantiation of the fake
    /// item `for<'a> fn(&'a A) -> Adt<'a, B>` with `A=B=u32`. Note how the item can therefore
    /// have trait clauses if some Adt does.
    /// Every free region, type and constant in the shape is a distinct generic parameter.
    FnPtr(FnPtrShape),
}

#[derive(Copy, Clone)]
pub struct SyntheticItemData<'tcx> {
    generics: &'tcx ty::Generics,
    clauses: &'tcx [ty::Clause<'tcx>],
    param_env: ty::ParamEnv<'tcx>,
    /// Dummy DefId used for `liberate_bound_regions`.
    late_bound_scope: Option<RDefId>,
}

/// This is a pretty criminal hack: I want to generate `ty::Generics` for my fake items. This
/// requires `DefId`s for the generic parameters. rustc has an affordance for creating new `DefId`s
/// (`tcx.create_def()`) but I could not figure out a way to use it that didn't end up ICEing
/// during metadata encoding. So instead I'm reusing the `DefId`s of generic parameters from `core`
/// functions.
#[derive(Copy, Clone)]
struct GenericParamDefIds {
    lt: RDefId,
    ty: RDefId,
    ct: RDefId,
}

impl GenericParamDefIds {
    fn construct<'tcx>(s: &impl BaseState<'tcx>) -> Self {
        let tcx = s.base().tcx;
        let pat = NamePattern::parse("core::array::repeat").unwrap();
        let repeat = def_path_def_ids(s, &pat, true)
            .unwrap_or_else(|err| panic!("could not resolve `core::array::repeat`: {err}"))
            .into_iter()
            .exactly_one()
            .unwrap();
        let generics = tcx.generics_of(repeat);
        let ty = generics
            .own_params
            .iter()
            .find(|param| matches!(param.kind, ty::GenericParamDefKind::Type { .. }))
            .unwrap_or_else(|| panic!("`core::array::repeat` has no type parameter"))
            .def_id;
        let ct = generics
            .own_params
            .iter()
            .find(|param| matches!(param.kind, ty::GenericParamDefKind::Const { .. }))
            .unwrap_or_else(|| panic!("`core::array::repeat` has no const parameter"))
            .def_id;
        let panic_info = tcx.require_lang_item(LangItem::PanicInfo, DUMMY_SP);
        let lt = tcx
            .generics_of(panic_info)
            .own_params
            .iter()
            .find(|param| matches!(param.kind, ty::GenericParamDefKind::Lifetime))
            .unwrap_or_else(|| panic!("`PanicInfo` has no lifetime parameter"))
            .def_id;
        GenericParamDefIds { lt, ty, ct }
    }
}

fn lifetime_param_name(index: usize) -> String {
    if index < 26 {
        format!("'{}", (b'a' + index as u8) as char)
    } else {
        format!("'r{index}")
    }
}

fn type_param_name(index: usize) -> String {
    if index < 26 {
        format!("{}", (b'A' + index as u8) as char)
    } else {
        format!("T{index}")
    }
}

impl SyntheticItem {
    pub fn name(&self) -> String {
        match self {
            SyntheticItem::Array => "<array>".to_string(),
            SyntheticItem::Slice => "<slice>".to_string(),
            SyntheticItem::Tuple(n) => format!("<tuple_{n}>"),
            SyntheticItem::Str => "<str>".to_string(),
            SyntheticItem::FnPtr(_) => "<fn_ptr>".to_string(),
        }
    }

    pub fn can_have_generics<'tcx>(&self, s: &impl BaseState<'tcx>) -> bool {
        !self.generics_of(s).own_params.is_empty()
    }

    pub fn generics_of<'tcx>(&self, s: &impl BaseState<'tcx>) -> &'tcx ty::Generics {
        self.data(s).generics
    }

    pub fn identity_args<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::GenericArgsRef<'tcx> {
        let tcx = s.base().tcx;
        tcx.mk_args_from_iter(
            self.generics_of(s)
                .own_params
                .iter()
                .map(|param| tcx.mk_param_from_def(param)),
        )
    }

    pub fn param_env<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::ParamEnv<'tcx> {
        self.data(s).param_env
    }

    pub fn late_bound_scope<'tcx>(&self, s: &impl BaseState<'tcx>) -> RDefId {
        self.data(s).late_bound_scope.unwrap()
    }

    /// Return the type of this constant parameter. `tcx.type_of` can't work here because we're
    /// reusing a dummy `DefId` for the generic parameter.
    pub fn const_param_ty<'tcx>(
        self,
        s: &impl BaseState<'tcx>,
        index: u32,
    ) -> Option<ty::Ty<'tcx>> {
        if let SyntheticItem::FnPtr(_) = self {
            self.data(s).clauses.iter().find_map(|clause| {
                if let ty::ClauseKind::ConstArgHasType(ct, ty) = clause.kind().skip_binder()
                    && let ty::ConstKind::Param(p) = ct.kind()
                    && p.index == index
                {
                    Some(ty)
                } else {
                    None
                }
            })
        } else {
            None
        }
    }

    pub fn predicates_defined_on<'tcx>(
        &self,
        s: &impl BaseState<'tcx>,
        def_id: DefId,
        direction: PredicateDirection,
    ) -> ItemPredicates<'tcx, DefId> {
        ItemPredicates::new(
            def_id,
            direction,
            self.data(s)
                .clauses
                .iter()
                .copied()
                .map(|clause| (clause, DUMMY_SP)),
        )
    }

    pub fn type_of<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::EarlyBinder<'tcx, ty::Ty<'tcx>> {
        let tcx = s.base().tcx;
        let args = self.identity_args(s);
        let type_of = match self {
            SyntheticItem::Array => {
                let item_ty = args[0].as_type().unwrap();
                let len = args[1].as_const().unwrap();
                ty::Ty::new_array_with_const_len(tcx, item_ty, len)
            }
            SyntheticItem::Slice => {
                let item_ty = args[0].as_type().unwrap();
                ty::Ty::new_slice(tcx, item_ty)
            }
            SyntheticItem::Tuple(_) => {
                let tys = args.iter().map(|arg| arg.as_type().unwrap());
                let tys = tcx.arena.alloc_from_iter(tys);
                ty::Ty::new_tup(tcx, tys)
            }
            SyntheticItem::Str => tcx.types.str_,
            SyntheticItem::FnPtr(shape) => shape.ty(s),
        };
        ty::EarlyBinder::bind(tcx, type_of)
    }

    fn data<'tcx>(&self, s: &impl BaseState<'tcx>) -> SyntheticItemData<'tcx> {
        if let Some(data) = s.with_global_cache(|c| c.synthetic_item_data.get(self).copied()) {
            return data;
        }
        let borrowed_param_def_ids = GenericParamDefIds::construct(s);
        s.with_global_cache(|c| c.synthetic_data(s, *self, borrowed_param_def_ids))
    }
}

impl<'tcx> GlobalCache<'tcx> {
    fn synthetic_data(
        &mut self,
        s: &impl BaseState<'tcx>,
        item: SyntheticItem,
        borrowed_param_def_ids: GenericParamDefIds,
    ) -> SyntheticItemData<'tcx> {
        if let Some(data) = self.synthetic_item_data.get(&item) {
            return *data;
        }
        let tcx = s.base().tcx;
        let mut generics = ty::Generics {
            parent: None,
            parent_count: 0,
            own_params: Default::default(),
            param_def_id_to_index: Default::default(),
            has_self: false,
            has_late_bound_regions: None,
        };
        // The synthetic item itself is hax-only. We still need rustc defs for its generic
        // parameters because rustc generic params carry a `DefId`, and const params need a
        // `type_of` entry. We do a little compiler crime to get such `DefId`s, see
        // `GenericParamDefIds`.
        let mut mk_param = |name: &str, kind: ty::GenericParamDefKind| {
            let name = Symbol::intern(name);
            let param_def_id = match kind {
                ty::GenericParamDefKind::Type { .. } => borrowed_param_def_ids.ty,
                ty::GenericParamDefKind::Const { .. } => borrowed_param_def_ids.ct,
                ty::GenericParamDefKind::Lifetime => borrowed_param_def_ids.lt,
            };
            let index = generics.own_params.len() as u32;
            let param_def = ty::GenericParamDef {
                name,
                def_id: param_def_id,
                index,
                kind,
                pure_wrt_drop: true,
            };
            let arg = tcx.mk_param_from_def(&param_def);
            generics.own_params.push(param_def);
            generics.param_def_id_to_index.insert(param_def_id, index);
            arg
        };

        let mut clauses = vec![];
        let sized_trait = tcx.lang_items().sized_trait().unwrap();
        match item {
            SyntheticItem::Array => {
                let t_arg = mk_param(
                    "T",
                    ty::GenericParamDefKind::Type {
                        has_default: false,
                        synthetic: false,
                    },
                );
                let n_arg = mk_param("N", ty::GenericParamDefKind::Const { has_default: false });

                let item_ty = t_arg.as_type().unwrap();
                let len = n_arg.as_const().unwrap();

                let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [item_ty]);
                clauses.push(ty_is_sized.upcast(tcx));
                let len_is_usize = ty::ClauseKind::ConstArgHasType(len, tcx.types.usize);
                clauses.push(len_is_usize.upcast(tcx));
            }
            SyntheticItem::Slice => {
                let t_arg = mk_param(
                    "T",
                    ty::GenericParamDefKind::Type {
                        has_default: false,
                        synthetic: false,
                    },
                );

                let item_ty = t_arg.as_type().unwrap();

                let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [item_ty]);
                clauses.push(ty_is_sized.upcast(tcx));
            }
            SyntheticItem::Tuple(len) => {
                let tys = (0..len).map(|i| {
                    let name = type_param_name(i);
                    let arg = mk_param(
                        &name,
                        ty::GenericParamDefKind::Type {
                            has_default: false,
                            synthetic: false,
                        },
                    );
                    arg.as_type().unwrap()
                });
                let tys = tcx.arena.alloc_from_iter(tys);

                // All types except the last one are sized.
                for ty in tys.iter().rev().skip(1).rev() {
                    let arg: ty::GenericArg = (*ty).into();
                    let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [arg]);
                    clauses.push(ty_is_sized.upcast(tcx));
                }
            }
            SyntheticItem::Str => {}
            SyntheticItem::FnPtr(shape) => {
                use rustc_infer::infer::TyCtxtInferExt;
                struct Params {
                    kinds: Vec<Option<ty::GenericParamDefKind>>,
                }

                impl Params {
                    fn insert(&mut self, index: usize, kind: ty::GenericParamDefKind) {
                        if self.kinds.len() <= index {
                            self.kinds.resize(index + 1, None);
                        }
                        self.kinds[index] = Some(kind);
                    }
                }

                impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for Params {
                    type Result = std::ops::ControlFlow<!>;

                    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) -> Self::Result {
                        if let ty::TyKind::Param(param) = ty.kind() {
                            self.insert(
                                param.index as usize,
                                ty::GenericParamDefKind::Type {
                                    has_default: false,
                                    synthetic: false,
                                },
                            );
                        }
                        ty.super_visit_with(self)
                    }

                    fn visit_region(&mut self, region: ty::Region<'tcx>) -> Self::Result {
                        if let ty::ReEarlyParam(param) = region.kind() {
                            self.insert(param.index as usize, ty::GenericParamDefKind::Lifetime);
                        }
                        std::ops::ControlFlow::Continue(())
                    }

                    fn visit_const(&mut self, ct: ty::Const<'tcx>) -> Self::Result {
                        if let ty::ConstKind::Param(param) = ct.kind() {
                            self.insert(
                                param.index as usize,
                                ty::GenericParamDefKind::Const { has_default: false },
                            );
                        }
                        ct.super_visit_with(self)
                    }
                }

                let sig = shape.sig(s);
                let mut params = Params { kinds: vec![] };
                sig.visit_with(&mut params);
                let mut next_lifetime = 0;
                let mut next_ty = 0;
                for (index, kind) in params.kinds.into_iter().enumerate() {
                    let kind = kind.expect("missing generic parameter in fn pointer shape");
                    let name = match kind {
                        ty::GenericParamDefKind::Lifetime => {
                            let name = lifetime_param_name(next_lifetime);
                            next_lifetime += 1;
                            name
                        }
                        ty::GenericParamDefKind::Type { .. } => {
                            let name = type_param_name(next_ty);
                            next_ty += 1;
                            name
                        }
                        ty::GenericParamDefKind::Const { .. } => format!("C{index}"),
                    };
                    mk_param(&name, kind);
                }

                clauses.extend(sig.skip_binder().inputs_and_output.iter().map(
                    |ty| -> ty::Clause<'tcx> {
                        sig.rebind(ty::TraitRef::new(tcx, sized_trait, [ty]))
                            .upcast(tcx)
                    },
                ));

                let infcx = tcx
                    .infer_ctxt()
                    .ignoring_regions()
                    .build(ty::TypingMode::PostAnalysis);
                let mut wf_clauses = rustc_trait_selection::traits::wf::obligations(
                    &infcx,
                    ty::ParamEnv::empty(),
                    rustc_hir::def_id::CRATE_DEF_ID,
                    0,
                    shape.ty(s).into(),
                    DUMMY_SP,
                )
                .into_iter()
                .flatten()
                .filter_map(|obligation| obligation.predicate.as_clause())
                .collect_vec();

                // Remove redundant clauses. This can avoid a silly recursive case where wf for the
                // fn ptr type may use a clause that references that same type.
                // See the `RecursiveProof` case in the fn-ptr-fn-traits.rs test.
                let mut index = 0;
                while index < wf_clauses.len() {
                    let clause = wf_clauses[index];
                    let follows_by_elaboration = ty::elaborate::elaborate(
                        tcx,
                        wf_clauses
                            .iter()
                            .enumerate()
                            .filter_map(|(i, clause)| (i != index).then_some(*clause)),
                    )
                    .elaborate_sized()
                    .any(|implied| implied == clause);
                    if follows_by_elaboration {
                        wf_clauses.remove(index);
                    } else {
                        index += 1;
                    }
                }
                clauses.extend(wf_clauses);
            }
        }

        let clauses = tcx.arena.alloc_from_iter(clauses);
        let data = SyntheticItemData {
            generics: Box::leak(Box::new(generics)),
            clauses,
            param_env: ty::ParamEnv::new(tcx, clauses.iter().copied()),
            late_bound_scope: matches!(item, SyntheticItem::FnPtr(_))
                .then(|| tcx.parent(borrowed_param_def_ids.lt)),
        };
        self.synthetic_item_data.insert(item, data);
        data
    }
}

impl ItemRef {
    pub fn translate_synthetic<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        synthetic: SyntheticItem,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef {
        let hax_def_id = DefId::make_synthetic(s, synthetic);
        ItemRef::translate_from_hax_def_id(s, hax_def_id, generics)
    }

    /// Take a fn pointer and construct a reference to the corresponding synthetic item.
    pub fn translate_fn_ptr<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        sig: ty::PolyFnSig<'tcx>,
    ) -> ItemRef {
        let (shape, args) = FnPtrShape::extract_shape(s.base().tcx, sig);
        Self::translate_synthetic(s, SyntheticItem::FnPtr(shape), args)
    }
}

/// Represents the "shape" of a function pointer, i.e. the most general signature we can obtain
/// from it without breaking the higher-kinded variables. E.g. `for<'a> fn(&'a u32) -> Adt<'a,
/// u32>` is considered to be an instantiation of the shape `for<'a> fn(&'a A) -> Adt<'a, B>` with
/// `A=B=u32`.
///
/// It's a `PolyFnSig` with erased `'tcx`, to avoid threading that lifetime through `hax::DefId`.
/// The hax infrastructure never escapes the compiler session, so this should be fine.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct FnPtrShape(ty::PolyFnSig<'static>);

impl FnPtrShape {
    fn erase<'tcx>(sig: ty::PolyFnSig<'tcx>) -> Self {
        // SAFETY: the extended lifetime never escapes the compiler session.
        Self(unsafe { std::mem::transmute::<ty::PolyFnSig<'tcx>, ty::PolyFnSig<'static>>(sig) })
    }

    fn sig<'tcx>(self, _s: &impl BaseState<'tcx>) -> ty::PolyFnSig<'tcx> {
        // SAFETY: we only use a single compiler session, so this is the same `'tcx`.
        unsafe { std::mem::transmute::<ty::PolyFnSig<'static>, ty::PolyFnSig<'tcx>>(self.0) }
    }

    fn ty<'tcx>(self, s: &impl BaseState<'tcx>) -> ty::Ty<'tcx> {
        ty::Ty::new_fn_ptr(s.base().tcx, self.sig(s))
    }
}
impl std::panic::RefUnwindSafe for FnPtrShape {}
impl std::panic::UnwindSafe for FnPtrShape {}

impl FnPtrShape {
    /// Replace each maximal type, region or constant that does not mention a locally-bound variable
    /// with a distinct generic parameter. We retain only the structure needed to keep higher-order
    /// variables correctly bound.
    fn extract_shape<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        sig: ty::PolyFnSig<'tcx>,
    ) -> (Self, ty::GenericArgsRef<'tcx>) {
        fn should_freshen<'tcx>(
            value: &impl ty::TypeVisitable<ty::TyCtxt<'tcx>>,
            binder_depth: u32,
        ) -> bool {
            struct MentionsBoundVar {
                binder_depth: u32,
            }

            impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for MentionsBoundVar {
                type Result = std::ops::ControlFlow<()>;

                fn visit_binder<T>(&mut self, binder: &ty::Binder<'tcx, T>) -> Self::Result
                where
                    T: ty::TypeVisitable<ty::TyCtxt<'tcx>>,
                {
                    self.binder_depth += 1;
                    let result = binder.super_visit_with(self);
                    self.binder_depth -= 1;
                    result
                }

                fn visit_ty(&mut self, ty: ty::Ty<'tcx>) -> Self::Result {
                    if matches!(
                        ty.kind(),
                        ty::TyKind::Bound(ty::BoundVarIndexKind::Bound(db), _)
                            if db.as_u32() < self.binder_depth
                    ) {
                        std::ops::ControlFlow::Break(())
                    } else {
                        ty.super_visit_with(self)
                    }
                }

                fn visit_region(&mut self, region: ty::Region<'tcx>) -> Self::Result {
                    if matches!(
                        region.kind(),
                        ty::ReBound(ty::BoundVarIndexKind::Bound(db), _)
                            if db.as_u32() < self.binder_depth
                    ) {
                        std::ops::ControlFlow::Break(())
                    } else {
                        std::ops::ControlFlow::Continue(())
                    }
                }

                fn visit_const(&mut self, ct: ty::Const<'tcx>) -> Self::Result {
                    if matches!(
                        ct.kind(),
                        ty::ConstKind::Bound(ty::BoundVarIndexKind::Bound(db), _)
                            if db.as_u32() < self.binder_depth
                    ) {
                        std::ops::ControlFlow::Break(())
                    } else {
                        ct.super_visit_with(self)
                    }
                }
            }

            value
                .visit_with(&mut MentionsBoundVar { binder_depth })
                .is_continue()
        }

        // Counts the number of parameters of each kind we'll need.
        #[derive(Default)]
        struct Counter {
            regions: u32,
            tys: u32,
            consts: u32,
            binder_depth: u32,
        }
        impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for Counter {
            type Result = std::ops::ControlFlow<!>;

            fn visit_binder<T>(&mut self, binder: &ty::Binder<'tcx, T>) -> Self::Result
            where
                T: ty::TypeVisitable<ty::TyCtxt<'tcx>>,
            {
                self.binder_depth += 1;
                let result = binder.super_visit_with(self);
                self.binder_depth -= 1;
                result
            }

            fn visit_ty(&mut self, ty: ty::Ty<'tcx>) -> Self::Result {
                if should_freshen(&ty, self.binder_depth) {
                    self.tys += 1;
                    std::ops::ControlFlow::Continue(())
                } else {
                    ty.super_visit_with(self)
                }
            }

            fn visit_region(&mut self, region: ty::Region<'tcx>) -> Self::Result {
                if should_freshen(&region, self.binder_depth) {
                    self.regions += 1;
                }
                std::ops::ControlFlow::Continue(())
            }

            fn visit_const(&mut self, ct: ty::Const<'tcx>) -> Self::Result {
                if should_freshen(&ct, self.binder_depth) {
                    self.consts += 1;
                    std::ops::ControlFlow::Continue(())
                } else {
                    ct.super_visit_with(self)
                }
            }
        }

        // Replaces each ty/region/const with a fresh param. We assign all lifetime indices first,
        // then types, then constants, to match rustc's generic argument ordering.
        struct Freshener<'tcx> {
            tcx: ty::TyCtxt<'tcx>,
            next_region: u32,
            next_ty: u32,
            next_const: u32,
            region_count: u32,
            ty_count: u32,
            binder_depth: u32,
            args: Vec<Option<ty::GenericArg<'tcx>>>,
        }
        impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for Freshener<'tcx> {
            fn cx(&self) -> ty::TyCtxt<'tcx> {
                self.tcx
            }

            fn fold_binder<T>(&mut self, binder: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
            where
                T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
            {
                self.binder_depth += 1;
                let binder = binder.super_fold_with(self);
                self.binder_depth -= 1;
                binder
            }

            fn fold_ty(&mut self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
                if should_freshen(&ty, self.binder_depth) {
                    let index = self.region_count + self.next_ty;
                    let name = type_param_name(self.next_ty as usize);
                    self.next_ty += 1;
                    self.args[index as usize] = Some(ty.into());
                    ty::Ty::new_param(self.tcx, index, Symbol::intern(&name))
                } else {
                    ty.super_fold_with(self)
                }
            }

            fn fold_region(&mut self, region: ty::Region<'tcx>) -> ty::Region<'tcx> {
                if should_freshen(&region, self.binder_depth) {
                    let index = self.next_region;
                    let name = lifetime_param_name(self.next_region as usize);
                    self.next_region += 1;
                    self.args[index as usize] = Some(region.into());
                    ty::Region::new_early_param(
                        self.tcx,
                        ty::EarlyParamRegion {
                            index,
                            name: Symbol::intern(&name),
                        },
                    )
                } else {
                    region
                }
            }

            fn fold_const(&mut self, ct: ty::Const<'tcx>) -> ty::Const<'tcx> {
                if should_freshen(&ct, self.binder_depth) {
                    let index = self.region_count + self.ty_count + self.next_const;
                    self.next_const += 1;
                    self.args[index as usize] = Some(ct.into());
                    ty::Const::new_param(
                        self.tcx,
                        ty::ParamConst {
                            index,
                            name: Symbol::intern(&format!("C{index}")),
                        },
                    )
                } else {
                    ct.super_fold_with(self)
                }
            }
        }

        let mut counts = Counter::default();
        sig.visit_with(&mut counts);
        let mut freshener = Freshener {
            tcx,
            next_region: 0,
            next_ty: 0,
            next_const: 0,
            region_count: counts.regions,
            ty_count: counts.tys,
            binder_depth: 0,
            args: vec![None; (counts.regions + counts.tys + counts.consts) as usize],
        };
        let shape = sig.fold_with(&mut freshener);
        let args = tcx.mk_args_from_iter(freshener.args.into_iter().map(Option::unwrap));
        (Self::erase(shape), args)
    }
}
