use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::fmt::Debug;
use std::mem;

use crate::hax;
use crate::hax::{BaseState, Symbol};
use rustc_middle::ty;

use super::translate_ctx::{ItemTransCtx, TransItemSourceKind};
use charon_lib::ast::*;
use charon_lib::utils::CycleDetector;

/// A level of binding for type-level variables. Each item has a top-level binding level
/// corresponding to the parameters and clauses to the items. We may then encounter inner binding
/// levels in the following cases:
/// - `for<..>` binders in predicates;
/// - `fn<..>` function pointer types;
/// - `dyn Trait` types, represented as `dyn<T: Trait>`;
/// - types in a trait declaration or implementation block;
/// - methods in a trait declaration or implementation block.
///
/// At each level, we store two things: a `GenericParams` that contains the parameters bound at
/// this level, and various maps from the rustc-internal indices to our indices.
#[derive(Debug, Default)]
pub(crate) struct BindingLevel<'tcx> {
    /// The parameters and predicates bound at this level.
    pub params: GenericParams,
    /// Whether this binding level exists in Hax's De Bruijn indices. `dyn Trait` introduces an
    /// existential binder in Charon that has no corresponding binder in rustc/Hax.
    pub counts_for_de_bruijn: bool,

    /// Rust makes the distinction between early and late-bound region parameters. We do not make
    /// this distinction, and merge early and late bound regions. For details, see:
    /// <https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/>
    /// <https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/>
    ///
    /// The map of early regions bound at this binder.
    pub early_region_vars: HashMap<hax::EarlyParamRegion, RegionId>,
    /// Extra early regions recovered by unerasing some regions that rustc keeps erased in args.
    /// Relevant for closures and inline consts. Hax represents these regions with placeholder
    /// regions.
    pub extra_early_region_vars: HashMap<hax::PlaceholderRegion, RegionId>,
    /// The map of named `ReLateParam` regions bound at this binder.
    pub late_named_region_vars: HashMap<hax::DefId, RegionId>,
    /// The map of anon `ReLateParam` regions bound at this binder, indexed by the scope `DefId`
    /// and variable index.
    pub late_anon_region_vars: HashMap<hax::DefId, Vec<RegionId>>,
    /// The map of `ReBound` regions bound at this binder, indexed by their bound variable index.
    pub bound_region_vars: Vec<RegionId>,
    /// Region added for the borrow of `self` accepted by a virtual impl method (e.g. `drop_glue` or
    /// `call`), or by a vtable shim.
    pub self_borrow_region: Option<RegionId>,
    /// RPITIT can cause region names to be reused. To avoid clashes in our output, we rename
    /// duplicate names.
    pub used_region_names: HashSet<Symbol>,

    /// The map from rust type variable indices to translated type variable indices. `None` marks
    /// inference-only parameters, which hax should normally never give us.
    pub type_vars: HashMap<u32, Option<TypeVarId>>,
    /// The map from rust const generic variables to translated const generic variable indices.
    pub const_generic_vars: HashMap<u32, ConstGenericVarId>,
    /// The map from trait predicates to the translated trait clause indices, and the number of
    /// bound higher-kinded regions.
    pub trait_preds: HashMap<hax::GenericPredicateId, (TraitClauseId, usize)>,

    /// Cache the translation of types. This harnesses the deduplication of `Ty` that hax does.
    // Important: we can't reuse type caches from earlier binders as the new binder may change what
    // a given variable resolves to.
    pub type_trans_cache: HashMap<hax::Ty<'tcx>, Ty>,
}

/// Small helper: we ignore some region names (when they are equal to "'_")
fn translate_region_name(s: hax::Symbol) -> Option<String> {
    let s = s.to_string();
    if s == "'_" { None } else { Some(s) }
}

fn translate_variance(variance: Option<&hax::Variance>) -> Variance {
    match variance {
        Some(hax::Variance::Covariant) => Variance::Covariant,
        Some(hax::Variance::Invariant) => Variance::Invariant,
        Some(hax::Variance::Contravariant) => Variance::Contravariant,
        Some(hax::Variance::Bivariant) => Variance::Bivariant,
        None => Variance::Unknown,
    }
}

impl<'tcx> BindingLevel<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            counts_for_de_bruijn: true,
            ..Default::default()
        }
    }

    pub(crate) fn new_dyn() -> Self {
        let mut level = Self::new();
        level.counts_for_de_bruijn = false;
        level
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_early_region(
        &mut self,
        region: hax::EarlyParamRegion,
        def_id: hax::DefId,
        variance: Variance,
        mutability: LifetimeMutability,
    ) -> RegionId {
        let name = if self.used_region_names.insert(region.name) {
            translate_region_name(region.name)
        } else {
            None
        };
        // Check that there are no late-bound regions
        assert!(
            self.bound_region_vars.is_empty(),
            "Early regions must be translated before late ones"
        );
        let rid = self.params.regions.push_with(|index| RegionParam {
            index,
            name,
            variance,
            mutability,
            late_bound: false,
        });
        self.early_region_vars.insert(region, rid);
        self.late_named_region_vars.insert(def_id, rid);
        rid
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_bound_region(
        &mut self,
        region: hax::BoundRegionKind,
        variance: Variance,
        late_param_def_id: Option<&hax::DefId>,
    ) -> RegionId {
        use crate::hax::BoundRegionKind::*;
        let (name, def_id) = match region {
            Anon => (None, None),
            NamedForPrinting(symbol) => (translate_region_name(symbol), None),
            Named(def_id, symbol) => (translate_region_name(symbol), Some(def_id)),
            ClosureEnv => (Some("env".to_owned()), None),
        };
        let rid = self.params.regions.push_with(|index| RegionParam {
            late_bound: true,
            ..RegionParam::new(index, name, variance)
        });
        if let Some(def_id) = def_id {
            self.late_named_region_vars.insert(def_id, rid);
        }
        if let Some(def_id) = late_param_def_id {
            self.late_anon_region_vars
                .entry(def_id.clone())
                .or_default()
                .push(rid);
        } else {
            self.bound_region_vars.push(rid);
        }
        rid
    }

    /// Extra lifetimes unerased from the closure arguments. Hax represents them with placeholder
    /// regions; they are parameters of the closure struct.
    pub fn push_unerased_region(&mut self, region: hax::PlaceholderRegion) {
        let region_id = self
            .params
            .regions
            .push_with(|index| RegionParam::new(index, None, Variance::Unknown));
        self.extra_early_region_vars.insert(region, region_id);
    }

    pub fn push_self_borrow_region(&mut self) -> RegionId {
        let region_id = self
            .params
            .regions
            .push_with(|index| RegionParam::new(index, None, Variance::Covariant));
        self.self_borrow_region = Some(region_id);
        region_id
    }

    pub(crate) fn push_type_var(
        &mut self,
        rid: u32,
        name: hax::Symbol,
        variance: Variance,
    ) -> TypeVarId {
        // Type vars comping from `impl Trait` arguments have as their name the whole `impl Trait`
        // expression. We turn it into an identifier.
        let mut name = name.to_string();
        if name
            .chars()
            .any(|c| !(c.is_ascii_alphanumeric() || c == '_'))
        {
            name = format!("T{rid}")
        }
        let var_id = self.params.types.push_with(|index| TypeParam {
            index,
            name,
            variance,
        });
        self.type_vars.insert(rid, Some(var_id));
        var_id
    }

    pub(crate) fn push_const_generic_var(&mut self, rid: u32, ty: Ty, name: hax::Symbol) {
        let var_id = self
            .params
            .const_generics
            .push_with(|index| ConstGenericParam {
                index,
                name: name.to_string(),
                ty,
            });
        self.const_generic_vars.insert(rid, var_id);
    }

    /// Add the binder's regions to this binding level. If `late_param_def_id` is `Some`, register
    /// them for `ReLateParam` lookup; otherwise, register them as this level's `ReBound`
    /// variables.
    pub(crate) fn push_bound_params(
        &mut self,
        binder: &hax::Binder<()>,
        late_param_def_id: Option<&hax::DefId>,
    ) {
        if late_param_def_id.is_none() {
            assert!(
                self.bound_region_vars.is_empty(),
                "Trying to use two binders at the same binding level"
            );
        }
        use crate::hax::BoundVariableKind::*;
        for p in &binder.bound_vars {
            match p {
                Region(region, variance) => {
                    let variance = translate_variance(variance.as_ref());
                    self.push_bound_region(region.clone(), variance, late_param_def_id);
                }
                Ty(_) => {
                    panic!("Unexpected locally bound type variable");
                }
                Const => {
                    panic!("Unexpected locally bound const generic variable");
                }
            }
        }
    }
}

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    /// Get the only binding level. Panics if there are other binding levels.
    pub(crate) fn the_only_binder(&self) -> &BindingLevel<'tcx> {
        assert_eq!(self.binding_levels.len(), 1);
        self.innermost_binder()
    }
    /// Get the only binding level. Panics if there are other binding levels.
    pub(crate) fn the_only_binder_mut(&mut self) -> &mut BindingLevel<'tcx> {
        assert_eq!(self.binding_levels.len(), 1);
        self.innermost_binder_mut()
    }

    pub(crate) fn outermost_binder(&self) -> &BindingLevel<'tcx> {
        self.binding_levels.outermost()
    }
    pub(crate) fn outermost_binder_mut(&mut self) -> &mut BindingLevel<'tcx> {
        self.binding_levels.outermost_mut()
    }
    pub(crate) fn innermost_binder(&self) -> &BindingLevel<'tcx> {
        self.binding_levels.innermost()
    }
    pub(crate) fn innermost_binder_mut(&mut self) -> &mut BindingLevel<'tcx> {
        self.binding_levels.innermost_mut()
    }

    pub(crate) fn outermost_generics(&self) -> &GenericParams {
        &self.outermost_binder().params
    }
    #[expect(dead_code)]
    pub(crate) fn outermost_generics_mut(&mut self) -> &mut GenericParams {
        &mut self.outermost_binder_mut().params
    }
    #[expect(dead_code)]
    pub(crate) fn innermost_generics(&self) -> &GenericParams {
        &self.innermost_binder().params
    }
    pub(crate) fn innermost_generics_mut(&mut self) -> &mut GenericParams {
        &mut self.innermost_binder_mut().params
    }

    pub(crate) fn lookup_bound_region(
        &mut self,
        span: Span,
        hax_dbid: hax::DebruijnIndex,
        var: hax::BoundVar,
    ) -> Result<RegionDbVar, Error> {
        if let Some((charon_dbid, level)) = self
            .binding_levels
            .iter_enumerated()
            .filter(|(_, l)| l.counts_for_de_bruijn)
            .nth(hax_dbid)
            && let Some(rid) = level.bound_region_vars.get(var)
        {
            Ok(DeBruijnVar::bound(charon_dbid, *rid))
        } else {
            raise_error!(
                self,
                span,
                "Unexpected error: could not find region '{hax_dbid}_{var}"
            )
        }
    }

    pub(crate) fn lookup_param<T: TyVisitable>(
        &mut self,
        span: Span,
        f: impl for<'a> Fn(&'a BindingLevel) -> Option<T>,
        mk_err: impl FnOnce() -> String,
    ) -> Result<T, Error> {
        for (depth, bl) in self.binding_levels.iter_enumerated() {
            if let Some(x) = f(bl) {
                return Ok(x.move_under_binders(depth));
            }
        }
        let err = mk_err();
        raise_error!(self, span, "Unexpected error: could not find {}", err)
    }

    pub(crate) fn lookup_early_region(
        &mut self,
        span: Span,
        region: &hax::EarlyParamRegion,
    ) -> Result<RegionDbVar, Error> {
        self.lookup_param(
            span,
            |bl| {
                bl.early_region_vars
                    .get(region)
                    .copied()
                    .map(DeBruijnVar::new_at_zero)
            },
            || format!("the region variable {region:?}"),
        )
    }

    pub(crate) fn lookup_late_param_region(
        &mut self,
        span: Span,
        region: &hax::LateParamRegion,
    ) -> Result<RegionDbVar, Error> {
        use hax::LateParamRegionKind::*;
        match &region.kind {
            Anon(index) | NamedAnon(index, _) => {
                let Some((dbid, regions)) =
                    self.binding_levels
                        .iter_enumerated()
                        .find_map(|(dbid, binder)| {
                            Some((dbid, binder.late_anon_region_vars.get(&region.scope)?))
                        })
                else {
                    raise_error!(
                        self,
                        span,
                        "Unexpected error: could not find the binder for late-bound region {region:?}"
                    )
                };
                let Some(region_id) = regions.get(*index as usize).copied() else {
                    raise_error!(
                        self,
                        span,
                        "Unexpected error: could not find the late-bound region variable {region:?}"
                    )
                };
                Ok(DeBruijnVar::bound(dbid, region_id))
            }
            Named(def_id, _) => self.lookup_param(
                span,
                |bl| {
                    bl.late_named_region_vars
                        .get(def_id)
                        .copied()
                        .map(DeBruijnVar::new_at_zero)
                },
                || format!("the late-bound region variable {region:?}"),
            ),
            ClosureEnv => {
                raise_error!(self, span, "Unexpected late-bound region: {region:?}")
            }
        }
    }

    pub(crate) fn lookup_type_var(
        &mut self,
        span: Span,
        param: &hax::ParamTy,
    ) -> Result<TypeDbVar, Error> {
        let var = self.lookup_param(
            span,
            |bl| {
                let var = *bl.type_vars.get(&param.index)?;
                Some(var.map(DeBruijnVar::new_at_zero))
            },
            || format!("the type variable {}", param.name),
        )?;
        if let Some(var) = var {
            Ok(var)
        } else {
            raise_error!(
                self,
                span,
                "Inference parameter {param:?} should have been replaced \
                with its known type before translation"
            );
        }
    }

    pub(crate) fn lookup_const_generic_var(
        &mut self,
        span: Span,
        param: &hax::ParamConst,
    ) -> Result<ConstGenericDbVar, Error> {
        self.lookup_param(
            span,
            |bl| {
                bl.const_generic_vars
                    .get(&param.index)
                    .copied()
                    .map(DeBruijnVar::new_at_zero)
            },
            || format!("the const generic variable {}", param.name),
        )
    }

    pub(crate) fn lookup_clause_var(
        &mut self,
        span: Span,
        id: &hax::GenericPredicateId,
    ) -> Result<(ClauseDbVar, usize), Error> {
        self.lookup_param(
            span,
            |bl| {
                let (id, regions) = bl.trait_preds.get(id).copied()?;
                Some((DeBruijnVar::new_at_zero(id), regions))
            },
            || format!("the trait clause variable {id:?}"),
        )
    }

    pub(crate) fn self_borrow_region(&self) -> Region {
        Region::Var(DeBruijnVar::new_at_zero(
            self.the_only_binder()
                .self_borrow_region
                .expect("item should have a borrow lifetime"),
        ))
    }

    pub(crate) fn self_borrow_generic_args(&mut self) -> GenericArgs {
        let mut generics = GenericArgs::empty();
        generics.regions.push(self.translate_erased_region());
        generics
    }

    pub(crate) fn self_borrow_params() -> GenericParams {
        let mut params = GenericParams::empty();
        params
            .regions
            .push_with(|index| RegionParam::new(index, None, Variance::Covariant));
        params
    }

    pub(crate) fn push_generic_params(
        &mut self,
        generics: &hax::TyGenerics<'tcx>,
    ) -> Result<(), Error> {
        for param in &generics.params {
            self.push_generic_param(param)?;
        }
        Ok(())
    }

    pub(crate) fn push_generic_param(
        &mut self,
        param: &hax::GenericParamDef<'tcx>,
    ) -> Result<(), Error> {
        let variance = translate_variance(param.variance.as_ref());
        match &param.kind {
            hax::GenericParamDefKind::Lifetime => {
                let region = hax::EarlyParamRegion {
                    index: param.index,
                    name: param.name,
                };
                let mutability = self
                    .t_ctx
                    .lt_mutability_computer
                    .compute_lifetime_mutability(
                        &self.hax_state,
                        self.item_src.def_id(),
                        param.index,
                    );
                let _ = self.innermost_binder_mut().push_early_region(
                    region,
                    param.def_id.clone(),
                    variance,
                    mutability,
                );
            }
            hax::GenericParamDefKind::Type {
                inference_value: Some(_),
                ..
            } => {
                // Inference-only type parameter, as used in closures and inline consts. We make
                // sure to get rid of them in hax, and error if found in Charon.
                self.innermost_binder_mut()
                    .type_vars
                    .insert(param.index, None);
            }
            hax::GenericParamDefKind::Type {
                inference_value: None,
                ..
            } => {
                let _ =
                    self.innermost_binder_mut()
                        .push_type_var(param.index, param.name, variance);
            }
            hax::GenericParamDefKind::Const { ty, .. } => {
                let span = self.def_span(&param.def_id);
                // The type should be primitive, meaning it shouldn't contain variables,
                // non-primitive adts, etc. As a result, we can use an empty context.
                let ty = self.translate_ty(span, ty)?;
                self.innermost_binder_mut()
                    .push_const_generic_var(param.index, ty, param.name);
            }
        }

        Ok(())
    }

    /// Add the generics and predicates of this item and its parents to the current context.
    #[tracing::instrument(skip(self, def))]
    fn push_generics_for_def(
        &mut self,
        def: &hax::FullDef<'tcx>,
        include_late_bound: bool,
    ) -> Result<(), Error> {
        if let Some(param_env) = def.param_env() {
            // Add generics from the parent item, recursively.
            if let Some(parent_item) = &param_env.soft_parent {
                let parent_def = self.hax_def(parent_item)?;
                self.push_generics_for_def(&parent_def, false)?;
            }
            let origin = Self::predicate_origin_for_def(def);
            self.push_param_env_without_parents(param_env, origin, include_late_bound)?;
        }
        Ok(())
    }

    fn predicate_origin_for_def(def: &hax::FullDef<'tcx>) -> PredicateOrigin {
        use crate::hax::FullDefKind;
        match &def.kind {
            FullDefKind::Adt(_)
            | FullDefKind::Variant(_)
            | FullDefKind::TyAlias(_)
            | FullDefKind::AssocTy(_) => PredicateOrigin::WhereClauseOnType,
            FullDefKind::Fn(_)
            | FullDefKind::FnPtr(_)
            | FullDefKind::AssocFn(_)
            | FullDefKind::Ctor(_)
            | FullDefKind::Closure(_)
            | FullDefKind::Const(_)
            | FullDefKind::AssocConst(_)
            | FullDefKind::Static(_) => PredicateOrigin::WhereClauseOnFn,
            FullDefKind::TraitImpl(_) | FullDefKind::InherentImpl(_) => {
                PredicateOrigin::WhereClauseOnImpl
            }
            FullDefKind::Trait(_) | FullDefKind::TraitAlias(_) => {
                PredicateOrigin::WhereClauseOnTrait
            }
            _ => panic!("Unexpected def: {:?}", def.def_id().kind),
        }
    }

    fn push_param_env_without_parents(
        &mut self,
        param_env: &hax::ParamEnv<'tcx>,
        origin: PredicateOrigin,
        include_late_bound: bool,
    ) -> Result<(), Error> {
        self.push_generic_params(&param_env.generics)?;
        for region in &param_env.extra_early_regions {
            self.innermost_binder_mut()
                .push_unerased_region(region.clone());
        }
        self.register_predicates(&param_env.predicates, origin)?;
        if include_late_bound && let Some(late_bound) = &param_env.late_bound {
            let level = self.innermost_binder_mut();
            level.push_bound_params(&late_bound.binder, Some(&late_bound.def_id));
            // Make the variable available for lookup using debruijn indices too, which we use when
            // translating signatures.
            level.bound_region_vars = level
                .late_anon_region_vars
                .get(&late_bound.def_id)
                .cloned()
                .unwrap_or_default();
        }
        Ok(())
    }

    /// Translate the generics and predicates of this item and its parents. This adds generic
    /// parameters and predicates to the current environment (as a binder in
    /// `self.binding_levels`). The constructed `GenericParams` can be recovered at the end using
    /// `self.into_generics()` and stored in the translated item.
    ///
    /// On top of the generics introduced by `push_generics_for_def`, this adds extra parameters
    /// required by the `TransItemSourceKind`.
    pub fn translate_item_generics(
        &mut self,
        _span: Span,
        def: &hax::FullDef<'tcx>,
        kind: &TransItemSourceKind,
    ) -> Result<(), Error> {
        assert!(self.binding_levels.is_empty());
        self.binding_levels.push(BindingLevel::new());
        // For closures, we only bind late-bound variables on the impl/methods, not the state struct.
        let include_late_bound =
            !matches!(def.kind(), hax::FullDefKind::Closure(_)) || kind.has_closure_late_params();
        self.push_generics_for_def(def, include_late_bound)?;

        if kind.has_self_borrow_region() {
            self.the_only_binder_mut().push_self_borrow_region();
        }

        self.innermost_binder_mut().params.check_consistency();
        Ok(())
    }

    /// Push a new binding level, run the provided function inside it, then return the bound value.
    pub(crate) fn inside_binder<F, U>(&mut self, kind: BinderKind, f: F) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        self.binding_levels.push(BindingLevel::new());

        // Call the continuation. Important: do not short-circuit on error here.
        let res = f(self);

        // Reset
        let params = self.binding_levels.pop().unwrap().params;

        // Return
        res.map(|skip_binder| Binder {
            kind,
            params,
            skip_binder,
        })
    }

    /// Push a new binding level with the given generics, then return the bound value.
    pub(crate) fn inside_item_binder<F, U>(
        &mut self,
        kind: BinderKind,
        owner: &hax::DefId,
        param_env: &hax::ParamEnv<'tcx>,
        predicate_origin: PredicateOrigin,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        let inner_hax_state = self.t_ctx.hax_state.clone().with_hax_owner(owner);
        let outer_hax_state = mem::replace(&mut self.hax_state, inner_hax_state);
        let ret = self.inside_binder(kind, |this| {
            this.push_param_env_without_parents(param_env, predicate_origin, true)?;
            this.innermost_binder().params.check_consistency();
            f(this)
        });
        self.hax_state = outer_hax_state;
        ret
    }

    /// Push a new binding level corresponding to the provided `def` for the duration of the inner
    /// function call.
    pub(crate) fn translate_binder_for_def<F, U>(
        &mut self,
        _span: Span,
        kind: BinderKind,
        def: &hax::FullDef<'tcx>,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        let param_env = def.param_env().unwrap();
        let origin = Self::predicate_origin_for_def(def);
        self.inside_item_binder(kind, def.def_id(), param_env, origin, |this| f(this))
    }

    /// Push a new binding level corresponding to the provided trait item binder for the duration
    /// of the inner function call.
    pub(crate) fn translate_trait_item_binder<F, T, U>(
        &mut self,
        _span: Span,
        kind: BinderKind,
        binder: &hax::TraitItemBinder<'tcx, T>,
        predicate_origin: PredicateOrigin,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self, &T) -> Result<U, Error>,
    {
        self.inside_item_binder(
            kind,
            &binder.def_id,
            &binder.param_env,
            predicate_origin,
            |this| f(this, &binder.skip_binder),
        )
    }

    /// Push a group of bound regions and call the continuation.
    /// We use this when diving into a `for<'a>`, or inside an arrow type (because
    /// it contains universally quantified regions).
    pub(crate) fn translate_region_binder<F, T, U>(
        &mut self,
        _span: Span,
        binder: &hax::Binder<T>,
        f: F,
    ) -> Result<RegionBinder<U>, Error>
    where
        F: FnOnce(&mut Self, &T) -> Result<U, Error>,
    {
        let binder = self.inside_binder(BinderKind::Other, |this| {
            this.innermost_binder_mut()
                .push_bound_params(&binder.rebind(()), None);
            f(this, binder.hax_skip_binder_ref())
        })?;
        // Convert to a region-only binder.
        Ok(RegionBinder {
            regions: binder.params.regions,
            outlives: binder.params.outlives,
            skip_binder: binder.skip_binder,
        })
    }

    pub(crate) fn into_generics(mut self) -> GenericParams {
        assert!(self.binding_levels.len() == 1);
        self.binding_levels.pop().unwrap().params
    }
}

/// Struct to compute the "mutability" of each lifetime.
#[derive(Default)]
pub struct LifetimeMutabilityComputer {
    lt_mutability: HashMap<hax::DefId, CycleDetector<HashSet<u32>>>,
}

impl LifetimeMutabilityComputer {
    /// Compute the mutability of one lifetime.
    pub(crate) fn compute_lifetime_mutability<'tcx>(
        &mut self,
        s: &impl BaseState<'tcx>,
        item: &hax::DefId,
        index: u32,
    ) -> LifetimeMutability {
        match self.compute_lifetime_mutabilities(s, item) {
            Some(set) => {
                if set.contains(&index) {
                    LifetimeMutability::Mutable
                } else {
                    LifetimeMutability::Shared
                }
            }
            None => LifetimeMutability::Unknown,
        }
    }

    /// Compute the "mutability" of each lifetime, i.e. whether this lifetime is used in a `&'a mut
    /// T` type or not. Returns a set of the known-mutable lifetimes for this ADT.
    fn compute_lifetime_mutabilities<'tcx>(
        &mut self,
        s: &impl BaseState<'tcx>,
        item: &hax::DefId,
    ) -> Option<&HashSet<u32>> {
        if !matches!(
            item.kind,
            hax::DefKind::Struct | hax::DefKind::Enum | hax::DefKind::Union | hax::DefKind::FnPtr
        ) {
            return None;
        }
        if self
            .lt_mutability
            .entry(item.clone())
            .or_default()
            .start_processing()
        {
            use crate::hax::SInto;
            use ty::{TypeSuperVisitable, TypeVisitable};

            struct LtMutabilityVisitor<'a, S> {
                s: &'a S,
                computer: &'a mut LifetimeMutabilityComputer,
                set: HashSet<u32>,
            }
            impl<'tcx, S: BaseState<'tcx>> ty::TypeVisitor<ty::TyCtxt<'tcx>> for LtMutabilityVisitor<'_, S> {
                fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
                    match ty.kind() {
                        ty::Ref(r, _, ty::Mutability::Mut)
                            if let ty::RegionKind::ReEarlyParam(r) = r.kind() =>
                        {
                            self.set.insert(r.index);
                        }
                        ty::Adt(adt, args) => {
                            let item = adt.did().sinto(self.s);
                            if let Some(mutabilities) =
                                self.computer.compute_lifetime_mutabilities(self.s, &item)
                            {
                                for arg in args.iter() {
                                    if let Some(r) = arg.as_region()
                                        && let ty::RegionKind::ReEarlyParam(r) = r.kind()
                                        && mutabilities.contains(&r.index)
                                    {
                                        self.set.insert(r.index);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                    ty.super_visit_with(self)
                }
            }
            let mut visitor = LtMutabilityVisitor {
                s,
                computer: self,
                set: HashSet::default(),
            };

            let tcx = s.base().tcx;
            if matches!(item.as_synthetic(s), Some(hax::SyntheticItem::FnPtr(_))) {
                item.type_of(s)
                    .instantiate_identity()
                    .skip_normalization()
                    .visit_with(&mut visitor);
            } else {
                let def_id = item.real_rust_def_id();
                let adt_def = tcx.adt_def(def_id);
                let generics = item.identity_args(s);
                for variant in adt_def.variants() {
                    for field in &variant.fields {
                        field.ty(tcx, generics).visit_with(&mut visitor);
                    }
                }
            }
            let set = visitor.set;

            self.lt_mutability
                .get_mut(item)
                .unwrap()
                .done_processing(set);
        }
        self.lt_mutability.get(item)?.as_processed()
    }
}
