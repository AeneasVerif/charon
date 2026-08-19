//! Make explicit the outlives predicates implied by item signatures.
use derive_generic_visitor::*;
use itertools::Itertools;
use std::mem;

use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};
use crate::utils::CycleDetector;

type BoundRegionOutlives = RegionBinder<RegionOutlives>;
type BoundTypeOutlives = RegionBinder<TypeOutlives>;

/// Explore a type and accumulate the outlives predicates it implies.
#[derive(Visitor)]
struct OutlivesGatherer<'a> {
    type_decls: &'a IndexMap<TypeDeclId, TypeDecl>,
    params: &'a mut GenericParams,
    regions_outlive: SeqHashSet<BoundRegionOutlives>,
    types_outlive: SeqHashSet<BoundTypeOutlives>,
    /// Regions that must be outlived by the type currently being visited.
    shorter_regions: Vec<Region>,
    /// Current binder depth.
    binder_depth: DeBruijnId,
}

impl<'a> OutlivesGatherer<'a> {
    fn new(params: &'a mut GenericParams, type_decls: &'a IndexMap<TypeDeclId, TypeDecl>) -> Self {
        Self {
            type_decls,
            regions_outlive: mem::take(&mut params.regions_outlive).into_iter().collect(),
            types_outlive: mem::take(&mut params.types_outlive).into_iter().collect(),
            params,
            shorter_regions: Vec::new(),
            binder_depth: DeBruijnId::ZERO,
        }
    }

    fn finish(self) {
        self.params
            .regions_outlive
            .extend(self.regions_outlive.into_iter().filter(|pred| {
                let OutlivesPred(longer, shorter) = pred.skip_binder;
                longer != shorter && longer != Region::Erased && shorter != Region::Erased
            }));
        self.params
            .types_outlive
            .extend(self.types_outlive.into_iter().filter(|pred| {
                let OutlivesPred(_, shorter) = pred.skip_binder;
                shorter != Region::Erased
            }));
    }

    fn with_shorter_region(
        &mut self,
        region: Region,
        f: impl FnOnce(&mut Self) -> ControlFlow<Infallible>,
    ) -> ControlFlow<Infallible> {
        if let Some(&shorter) = self.shorter_regions.last() {
            self.regions_outlive
                .insert(RegionBinder::empty(OutlivesPred(region, shorter)));
        }
        self.shorter_regions.push(region);
        f(self)?;
        self.shorter_regions.pop().unwrap();
        Continue(())
    }
}

impl VisitorWithBinderDepth for OutlivesGatherer<'_> {
    fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
        &mut self.binder_depth
    }
}

impl VisitAst for OutlivesGatherer<'_> {
    fn visit<T: AstVisitable>(&mut self, value: &T) -> ControlFlow<Self::Break> {
        VisitWithBinderDepth::new(self).visit(value)
    }

    fn visit_ty(&mut self, ty: &Ty) -> ControlFlow<Self::Break> {
        match ty.kind() {
            TyKind::TypeVar(_) | TyKind::TraitType(..)
                if let Some(ty) = ty.clone().move_from_under_binders(self.binder_depth) =>
            {
                if let Some(&shorter) = self.shorter_regions.last() {
                    self.types_outlive
                        .insert(RegionBinder::empty(OutlivesPred(ty.clone(), shorter)));
                }
            }
            TyKind::Adt(type_ref)
                if let TypeId::Adt(type_id) = type_ref.id
                    && let Some(decl) = self.type_decls.get(type_id)
                    && let Some(generics) = type_ref
                        .generics
                        .clone()
                        .move_from_under_binders(self.binder_depth) =>
            {
                self.regions_outlive.extend(
                    decl.generics
                        .regions_outlive
                        .iter()
                        .cloned()
                        .map(|pred| pred.substitute(&generics)),
                );
                self.types_outlive.extend(
                    decl.generics
                        .types_outlive
                        .iter()
                        .cloned()
                        .map(|pred| pred.substitute(&generics)),
                );
            }
            _ => {}
        }
        match ty.kind() {
            TyKind::Ref(region @ (Region::Static | Region::Var(_)), _, _)
                if let Some(region) = (*region).move_from_under_binders(self.binder_depth) =>
            {
                self.with_shorter_region(region, |this| this.visit_inner(ty))
            }
            _ => self.visit_inner(ty),
        }
    }

    fn enter_region(&mut self, region: &Region) {
        if let Some(longer @ Region::Var(_)) = (*region).move_from_under_binders(self.binder_depth)
            && let Some(&shorter) = self.shorter_regions.last()
        {
            self.regions_outlive
                .insert(RegionBinder::empty(OutlivesPred(longer, shorter)));
        }
    }
}

struct ClosureOutlivesComputer<'a> {
    type_decls: &'a mut IndexMap<TypeDeclId, TypeDecl>,
    /// Map of types we want to process.
    closure_tys: SeqHashMap<TypeDeclId, CycleDetector<()>>,
}

impl<'a> ClosureOutlivesComputer<'a> {
    fn new(type_decls: &'a mut IndexMap<TypeDeclId, TypeDecl>) -> Self {
        let closure_tys = type_decls
            .iter()
            .filter(|decl| matches!(decl.src, TypeSource::Closure { .. }))
            .map(|decl| (decl.def_id, CycleDetector::Unprocessed))
            .collect();
        Self {
            type_decls,
            closure_tys,
        }
    }

    fn compute_all(mut self) {
        for type_id in self.closure_tys.keys().cloned().collect_vec() {
            self.compute(type_id);
        }
    }

    fn compute(&mut self, type_id: TypeDeclId) {
        if self.closure_tys[&type_id].start_processing() {
            let mut dependencies = Vec::new();
            self.type_decls[type_id]
                .kind
                .dyn_visit(|type_ref: &TypeDeclRef| {
                    if let TypeId::Adt(type_id) = type_ref.id
                        && self.closure_tys.get(&type_id).is_some()
                    {
                        dependencies.push(type_id);
                    }
                });
            for dependency in dependencies {
                self.compute(dependency);
            }

            let mut params = mem::take(&mut self.type_decls[type_id].generics);
            let mut visitor = OutlivesGatherer::new(&mut params, self.type_decls);
            visitor.visit(&self.type_decls[type_id].kind);
            visitor.finish();
            self.type_decls[type_id].generics = params;
            self.closure_tys[&type_id].done_processing(());
        }
        assert!(
            matches!(self.closure_tys[&type_id], CycleDetector::Processed(_)),
            "closure type declarations unexpectedly form a cycle"
        );
    }
}

pub struct Transform;

impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let type_decls = &mut ctx.translated.type_decls;

        // Rustc gives us explicit outlives for ADTs, but we make fake ADTs for closures, so we
        // infer their outlives predicates here. Thankfully they can't be recursive, which makes
        // the implementation much easier than having to deal with all ADTs.
        ClosureOutlivesComputer::new(type_decls).compute_all();

        for fun_decl in &mut ctx.translated.fun_decls {
            let mut visitor = OutlivesGatherer::new(&mut fun_decl.generics, type_decls);
            visitor.visit(&fun_decl.signature);
            visitor.finish();
        }

        for timpl in &mut ctx.translated.trait_impls {
            let mut visitor = OutlivesGatherer::new(&mut timpl.generics, type_decls);
            visitor.visit(&timpl.impl_trait);
            visitor.finish();
        }
    }
}
