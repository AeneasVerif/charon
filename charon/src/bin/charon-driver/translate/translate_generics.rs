use crate::translate::translate_ctx::TraitImplSource;

use super::translate_ctx::{ItemTransCtx, TransItemSourceKind};
use charon_lib::ast::*;
use charon_lib::ids::IndexVec;
use std::collections::HashMap;
use std::fmt::Debug;

/// A level of binding for type-level variables. Each item has a top-level binding level
/// corresponding to the parameters and clauses to the items. We may then encounter inner binding
/// levels in the following cases:
/// - `for<..>` binders in predicates;
/// - `fn<..>` function pointer types;
/// - `dyn Trait` types, represented as `dyn<T: Trait>` (TODO);
/// - types in a trait declaration or implementation block (TODO);
/// - methods in a trait declaration or implementation block (TODO).
///
/// At each level, we store two things: a `GenericParams` that contains the parameters bound at
/// this level, and various maps from the rustc-internal indices to our indices.
#[derive(Debug, Default)]
pub(crate) struct BindingLevel {
    /// The parameters and predicates bound at this level.
    pub params: GenericParams,
    /// Whether this binder corresponds to an item (method, type) or not (`for<..>` predicate, `fn`
    /// pointer, etc). This indicates whether it corresponds to a rustc `ParamEnv` and therefore
    /// whether we should resolve rustc variables there.
    pub is_item_binder: bool,
    /// Rust makes the distinction between early and late-bound region parameters. We do not make
    /// this distinction, and merge early and late bound regions. For details, see:
    /// <https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/>
    /// <https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/>
    ///
    /// The map from rust early regions to translated region indices.
    pub early_region_vars: HashMap<hax::EarlyParamRegion, RegionId>,
    /// The map from rust late/bound regions to translated region indices.
    pub bound_region_vars: Vec<RegionId>,
    /// Region added for the lifetime bound in the signature of the `call`/`call_mut` methods.
    pub closure_call_method_region: Option<RegionId>,
    /// The map from rust type variable indices to translated type variable indices.
    pub type_vars_map: HashMap<u32, TypeVarId>,
    /// The map from rust const generic variables to translate const generic variable indices.
    pub const_generic_vars_map: HashMap<u32, ConstGenericVarId>,
    /// The types of the captured variables, when we're translating a closure item. This is
    /// translated early because this translation requires adding new lifetime generics to the
    /// current binder.
    pub closure_upvar_tys: Option<IndexVec<FieldId, Ty>>,
    /// The regions we added for the upvars.
    pub closure_upvar_regions: Vec<RegionId>,
    /// Cache the translation of types. This harnesses the deduplication of `Ty` that hax does.
    // Important: we can't reuse type caches from earlier binders as the new binder may change what
    // a given variable resolves to.
    pub type_trans_cache: HashMap<hax::Ty, Ty>,
}

/// Small helper: we ignore some region names (when they are equal to "'_")
fn translate_region_name(s: hax::Symbol) -> Option<String> {
    let s = s.to_string();
    if s == "'_" { None } else { Some(s) }
}

impl BindingLevel {
    pub(crate) fn new(is_item_binder: bool) -> Self {
        Self {
            is_item_binder,
            ..Default::default()
        }
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_early_region(&mut self, region: hax::EarlyParamRegion) -> RegionId {
        let name = translate_region_name(region.name);
        // Check that there are no late-bound regions
        assert!(
            self.bound_region_vars.is_empty(),
            "Early regions must be translated before late ones"
        );
        let rid = self
            .params
            .regions
            .push_with(|index| RegionParam { index, name });
        self.early_region_vars.insert(region, rid);
        rid
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_bound_region(&mut self, region: hax::BoundRegionKind) -> RegionId {
        use hax::BoundRegionKind::*;
        let name = match region {
            Anon => None,
            NamedForPrinting(symbol) | Named(_, symbol) => translate_region_name(symbol),
            ClosureEnv => Some("@env".to_owned()),
        };
        let rid = self
            .params
            .regions
            .push_with(|index| RegionParam { index, name });
        self.bound_region_vars.push(rid);
        rid
    }

    /// Add a region for an upvar in a closure.
    pub fn push_upvar_region(&mut self) -> RegionId {
        // We musn't push to `bound_region_vars` because that will contain the higher-kinded
        // signature lifetimes (if any) and they must be lookup-able.
        let region_id = self
            .params
            .regions
            .push_with(|index| RegionParam { index, name: None });
        self.closure_upvar_regions.push(region_id);
        region_id
    }

    pub(crate) fn push_type_var(&mut self, rid: u32, name: hax::Symbol) -> TypeVarId {
        // Type vars comping from `impl Trait` arguments have as their name the whole `impl Trait`
        // expression. We turn it into an identifier.
        let mut name = name.to_string();
        if name
            .chars()
            .any(|c| !(c.is_ascii_alphanumeric() || c == '_'))
        {
            name = format!("T{rid}")
        }
        let var_id = self
            .params
            .types
            .push_with(|index| TypeParam { index, name });
        self.type_vars_map.insert(rid, var_id);
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
        self.const_generic_vars_map.insert(rid, var_id);
    }

    /// Translate a binder of regions by appending the stored reguions to the given vector.
    pub(crate) fn push_params_from_binder(&mut self, binder: hax::Binder<()>) -> Result<(), Error> {
        assert!(
            self.bound_region_vars.is_empty(),
            "Trying to use two binders at the same binding level"
        );
        use hax::BoundVariableKind::*;
        for p in binder.bound_vars {
            match p {
                Region(region) => {
                    self.push_bound_region(region);
                }
                Ty(_) => {
                    panic!("Unexpected locally bound type variable");
                }
                Const => {
                    panic!("Unexpected locally bound const generic variable");
                }
            }
        }
        Ok(())
    }
}

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    /// Get the only binding level. Panics if there are other binding levels.
    pub(crate) fn the_only_binder(&self) -> &BindingLevel {
        assert_eq!(self.binding_levels.len(), 1);
        self.innermost_binder()
    }
    /// Get the only binding level. Panics if there are other binding levels.
    pub(crate) fn the_only_binder_mut(&mut self) -> &mut BindingLevel {
        assert_eq!(self.binding_levels.len(), 1);
        self.innermost_binder_mut()
    }

    pub(crate) fn outermost_binder(&self) -> &BindingLevel {
        self.binding_levels.outermost()
    }
    pub(crate) fn outermost_binder_mut(&mut self) -> &mut BindingLevel {
        self.binding_levels.outermost_mut()
    }
    pub(crate) fn innermost_binder(&self) -> &BindingLevel {
        self.binding_levels.innermost()
    }
    pub(crate) fn innermost_binder_mut(&mut self) -> &mut BindingLevel {
        self.binding_levels.innermost_mut()
    }

    pub(crate) fn outermost_generics(&self) -> &GenericParams {
        &self.outermost_binder().params
    }
    #[expect(dead_code)]
    pub(crate) fn outermost_generics_mut(&mut self) -> &mut GenericParams {
        &mut self.outermost_binder_mut().params
    }
    pub(crate) fn innermost_generics(&self) -> &GenericParams {
        &self.innermost_binder().params
    }
    pub(crate) fn innermost_generics_mut(&mut self) -> &mut GenericParams {
        &mut self.innermost_binder_mut().params
    }

    pub(crate) fn lookup_bound_region(
        &mut self,
        span: Span,
        dbid: hax::DebruijnIndex,
        var: hax::BoundVar,
    ) -> Result<RegionDbVar, Error> {
        let dbid = DeBruijnId::new(dbid);
        if let Some(rid) = self
            .binding_levels
            .get(dbid)
            .and_then(|bl| bl.bound_region_vars.get(var))
        {
            Ok(DeBruijnVar::bound(dbid, *rid))
        } else {
            raise_error!(
                self,
                span,
                "Unexpected error: could not find region '{dbid}_{var}"
            )
        }
    }

    pub(crate) fn lookup_param<Id: Copy>(
        &mut self,
        span: Span,
        f: impl for<'a> Fn(&'a BindingLevel) -> Option<Id>,
        mk_err: impl FnOnce() -> String,
    ) -> Result<DeBruijnVar<Id>, Error> {
        for (dbid, bl) in self.binding_levels.iter_enumerated() {
            if let Some(id) = f(bl) {
                return Ok(DeBruijnVar::bound(dbid, id));
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
            |bl| bl.early_region_vars.get(region).copied(),
            || format!("the region variable {region:?}"),
        )
    }

    pub(crate) fn lookup_type_var(
        &mut self,
        span: Span,
        param: &hax::ParamTy,
    ) -> Result<TypeDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.type_vars_map.get(&param.index).copied(),
            || format!("the type variable {}", param.name),
        )
    }

    pub(crate) fn lookup_const_generic_var(
        &mut self,
        span: Span,
        param: &hax::ParamConst,
    ) -> Result<ConstGenericDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.const_generic_vars_map.get(&param.index).copied(),
            || format!("the const generic variable {}", param.name),
        )
    }

    pub(crate) fn lookup_clause_var(
        &mut self,
        span: Span,
        mut id: usize,
    ) -> Result<ClauseDbVar, Error> {
        // The clause indices returned by hax count clauses in order, starting from the parentmost.
        // While adding clauses to a binding level we already need to translate types and clauses,
        // so the innermost item binder may not have all the clauses yet. Hence for that binder we
        // ignore the clause count.
        let innermost_item_binder_id = self
            .binding_levels
            .iter_enumerated()
            .find(|(_, bl)| bl.is_item_binder)
            .unwrap()
            .0;
        // Iterate over the binders, starting from the outermost.
        for (dbid, bl) in self.binding_levels.iter_enumerated().rev() {
            let num_clauses_bound_at_this_level = bl.params.trait_clauses.elem_count();
            if id < num_clauses_bound_at_this_level || dbid == innermost_item_binder_id {
                let id = TraitClauseId::from_usize(id);
                return Ok(DeBruijnVar::bound(dbid, id));
            } else {
                id -= num_clauses_bound_at_this_level
            }
        }
        // Actually unreachable
        raise_error!(
            self,
            span,
            "Unexpected error: could not find clause variable {}",
            id
        )
    }

    pub(crate) fn push_generic_params(&mut self, generics: &hax::TyGenerics) -> Result<(), Error> {
        for param in &generics.params {
            self.push_generic_param(param)?;
        }
        Ok(())
    }

    pub(crate) fn push_generic_param(&mut self, param: &hax::GenericParamDef) -> Result<(), Error> {
        match &param.kind {
            hax::GenericParamDefKind::Lifetime => {
                let region = hax::EarlyParamRegion {
                    index: param.index,
                    name: param.name.clone(),
                };
                let _ = self.innermost_binder_mut().push_early_region(region);
            }
            hax::GenericParamDefKind::Type { .. } => {
                let _ = self
                    .innermost_binder_mut()
                    .push_type_var(param.index, param.name);
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

    // The parameters (and in particular the lifetimes) are split between
    // early bound and late bound parameters. See those blog posts for explanations:
    // https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
    // https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
    // Note that only lifetimes can be late bound at the moment.
    //
    // [TyCtxt.generics_of] gives us the early-bound parameters. We add the late-bound parameters
    // here.
    fn push_late_bound_generics_for_def(
        &mut self,
        _span: Span,
        def: &hax::FullDef,
    ) -> Result<(), Error> {
        if let hax::FullDefKind::Fn { sig, .. } | hax::FullDefKind::AssocFn { sig, .. } = def.kind()
        {
            let innermost_binder = self.innermost_binder_mut();
            assert!(innermost_binder.bound_region_vars.is_empty());
            innermost_binder.push_params_from_binder(sig.rebind(()))?;
        }
        Ok(())
    }

    /// Add the generics and predicates of this item and its parents to the current context.
    #[tracing::instrument(skip(self, span, def))]
    fn push_generics_for_def(&mut self, span: Span, def: &hax::FullDef) -> Result<(), Error> {
        trace!("{:?}", def.param_env());
        // Add generics from the parent item, recursively (recursivity is important for closures,
        // as they can be nested).
        if let Some(parent_item) = def.typing_parent(self.hax_state()) {
            let parent_def = self.hax_def(&parent_item)?;
            self.push_generics_for_def(span, &parent_def)?;
        }
        self.push_generics_for_def_without_parents(span, def)?;
        Ok(())
    }

    /// Add the generics and predicates of this item. This does not include the parent generics;
    /// use `push_generics_for_def` to get the full list.
    fn push_generics_for_def_without_parents(
        &mut self,
        _span: Span,
        def: &hax::FullDef,
    ) -> Result<(), Error> {
        use hax::FullDefKind;
        if let Some(param_env) = def.param_env() {
            // Add the generic params.
            self.push_generic_params(&param_env.generics)?;
            // Add the predicates.
            let origin = match &def.kind {
                FullDefKind::Adt { .. }
                | FullDefKind::TyAlias { .. }
                | FullDefKind::AssocTy { .. } => PredicateOrigin::WhereClauseOnType,
                FullDefKind::Fn { .. }
                | FullDefKind::AssocFn { .. }
                | FullDefKind::Closure { .. }
                | FullDefKind::Const { .. }
                | FullDefKind::AssocConst { .. }
                | FullDefKind::Static { .. } => PredicateOrigin::WhereClauseOnFn,
                FullDefKind::TraitImpl { .. } | FullDefKind::InherentImpl { .. } => {
                    PredicateOrigin::WhereClauseOnImpl
                }
                FullDefKind::Trait { .. } | FullDefKind::TraitAlias { .. } => {
                    PredicateOrigin::WhereClauseOnTrait
                }
                _ => panic!("Unexpected def: {:?}", def.def_id().kind),
            };
            self.register_predicates(&param_env.predicates, origin.clone())?;
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
        span: Span,
        def: &hax::FullDef,
        kind: &TransItemSourceKind,
    ) -> Result<(), Error> {
        assert!(self.binding_levels.len() == 0);
        self.binding_levels.push(BindingLevel::new(true));
        self.push_generics_for_def(span, def)?;
        self.push_late_bound_generics_for_def(span, def)?;

        if let hax::FullDefKind::Closure { args, .. } = def.kind() {
            // Add the lifetime generics coming from the upvars. We translate the upvar types early
            // to know what lifetimes are needed.
            let upvar_tys = self.translate_closure_upvar_tys(span, args)?;
            // Add new lifetimes params to replace the erased ones.
            let upvar_tys = upvar_tys.replace_erased_regions(|| {
                let region_id = self.the_only_binder_mut().push_upvar_region();
                Region::Var(DeBruijnVar::new_at_zero(region_id))
            });
            self.the_only_binder_mut().closure_upvar_tys = Some(upvar_tys);

            // Add the lifetime generics coming from the higher-kindedness of the signature.
            if let TransItemSourceKind::TraitImpl(TraitImplSource::Closure(..))
            | TransItemSourceKind::ClosureMethod(..)
            | TransItemSourceKind::ClosureAsFnCast = kind
            {
                self.the_only_binder_mut()
                    .push_params_from_binder(args.fn_sig.rebind(()))?;
            }
            if let TransItemSourceKind::ClosureMethod(ClosureKind::Fn | ClosureKind::FnMut) = kind {
                // Add the lifetime generics coming from the method itself.
                let rid = self
                    .the_only_binder_mut()
                    .params
                    .regions
                    .push_with(|index| RegionParam { index, name: None });
                self.the_only_binder_mut().closure_call_method_region = Some(rid);
            }
        }

        self.innermost_binder_mut().params.check_consistency();
        Ok(())
    }

    /// Push a new binding level, run the provided function inside it, then return the bound value.
    pub(crate) fn inside_binder<F, U>(
        &mut self,
        kind: BinderKind,
        is_item_binder: bool,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        assert!(!self.binding_levels.is_empty());
        self.binding_levels.push(BindingLevel::new(is_item_binder));

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

    /// Push a new binding level corresponding to the provided `def` for the duration of the inner
    /// function call.
    pub(crate) fn translate_binder_for_def<F, U>(
        &mut self,
        span: Span,
        kind: BinderKind,
        def: &hax::FullDef,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        self.inside_binder(kind, true, |this| {
            this.push_generics_for_def_without_parents(span, def)?;
            this.push_late_bound_generics_for_def(span, def)?;
            this.innermost_binder().params.check_consistency();
            f(this)
        })
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
        let binder = self.inside_binder(BinderKind::Other, false, |this| {
            this.innermost_binder_mut()
                .push_params_from_binder(binder.rebind(()))?;
            f(this, binder.hax_skip_binder_ref())
        })?;
        // Convert to a region-only binder.
        Ok(RegionBinder {
            regions: binder.params.regions,
            skip_binder: binder.skip_binder,
        })
    }

    pub(crate) fn into_generics(mut self) -> GenericParams {
        assert!(self.binding_levels.len() == 1);
        self.binding_levels.pop().unwrap().params
    }
}
