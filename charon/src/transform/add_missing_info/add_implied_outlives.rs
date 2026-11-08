//! Make explicit the outlives predicates implied by the well-formedness of a type.
use derive_generic_visitor::*;
use itertools::Itertools;
use std::mem;

use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};
use crate::utils::CycleDetector;

#[derive(Default)]
struct OutlivesAtBinder {
    outlives: SeqHashSet<PolyOutlivesPred>,
    /// The lifetime of the innermost reference we're inside of. When going under a binder, we keep
    /// it there.
    ///
    /// E.g. in `&'a for<'b> fn(&'b u32, &'c u32)`, the `'a` stays on the outer binder, and we use
    /// that to add `'c: 'a` but we don't add `'b: 'a` since `'b` is not visible from where `'a`
    /// is.
    shorter_region: Option<Region>,
}

impl OutlivesAtBinder {
    fn finish(self, outlives: &mut Vec<PolyOutlivesPred>) {
        debug_assert!(self.shorter_region.is_none());
        let mut predicates: SeqHashSet<_> = mem::take(outlives).into_iter().collect();
        predicates.extend(self.outlives);
        outlives.extend(predicates.into_iter().filter(|pred| {
            let OutlivesPred(longer, shorter) = &pred.skip_binder;
            longer != shorter && !longer.is_erased() && !shorter.is_erased()
        }));
    }
}

/// Explore a type and accumulate the outlives predicates it implies.
#[derive(Visitor)]
struct OutlivesGatherer<'a> {
    type_decls: &'a IndexMap<TypeDeclId, TypeDecl>,
    trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    item_params: &'a mut GenericParams,
    binders: BindingStack<OutlivesAtBinder>,
}

impl<'a> OutlivesGatherer<'a> {
    fn new(
        item_params: &'a mut GenericParams,
        type_decls: &'a IndexMap<TypeDeclId, TypeDecl>,
        trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    ) -> Self {
        Self {
            type_decls,
            trait_decls,
            item_params,
            binders: BindingStack::new(OutlivesAtBinder::default()),
        }
    }

    fn finish(mut self) {
        let outlives = self.binders.pop().unwrap();
        debug_assert!(self.binders.is_empty());
        outlives.finish(&mut self.item_params.outlives);
    }

    fn add_outlives(&mut self, pred: PolyOutlivesPred) {
        let (pred, level) = self.binders.place_at_outermost(&pred);
        level.outlives.insert(pred);
    }
    fn add_outliving_region(&mut self, longer: &Region) {
        // Find the innermost region that affects `longer`: it needs to be bound at a level where
        // `longer` can be moved to.
        let Some((bound_depth, pred)) =
            self.binders.iter_enumerated().find_map(|(depth, binder)| {
                let shorter = binder.shorter_region.clone()?;
                let longer = longer.clone().move_from_under_binders(depth)?;
                let pred = RegionBinder::empty(OutlivesPred(longer, shorter));
                Some((depth, pred))
            })
        else {
            return;
        };
        // Place the predicate at the outermost level.
        let (pred, level) = self.binders[bound_depth..].place_at_outermost(&pred);
        level.outlives.insert(pred);
    }

    fn with_shorter_region(
        &mut self,
        region: Region,
        f: impl FnOnce(&mut Self) -> ControlFlow<Infallible>,
    ) -> ControlFlow<Infallible> {
        self.add_outliving_region(&region);
        let previous = self.binders.innermost_mut().shorter_region.replace(region);
        let result = f(self);
        self.binders.innermost_mut().shorter_region = previous;
        result
    }
}

impl VisitAstMut for OutlivesGatherer<'_> {
    fn visit_binder<T: AstVisitable>(
        &mut self,
        binder: &mut Binder<T>,
    ) -> ControlFlow<Self::Break> {
        self.binders.push(OutlivesAtBinder::default());
        let result = self.visit_inner(binder);
        self.binders
            .pop()
            .unwrap()
            .finish(&mut binder.params.outlives);
        result
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        binder: &mut RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        self.binders.push(OutlivesAtBinder::default());
        let result = self.visit_inner(binder);
        self.binders.pop().unwrap().finish(&mut binder.outlives);
        result
    }

    fn visit_ty(&mut self, ty: &mut Ty) -> ControlFlow<Self::Break> {
        if let TyKind::TraitType(proof, type_id, args) = ty.kind()
            && let Some(decl) = self.trait_decls.get(proof.trait_id())
            && let Some(assoc) = decl.types.get(*type_id)
        {
            // Instantiate the trait parameters under the GAT binder, then the GAT parameters.
            let assoc = assoc.clone().substitute_with_tref(proof);
            for pred in assoc.params.outlives.substitute_inner_binder(args) {
                self.add_outlives(pred);
            }
        }
        match ty.kind() {
            TyKind::TypeVar(_) | TyKind::TraitType(..) => {
                self.add_outliving_region(&Region::Lub(ty.clone()));
                // `T::Assoc: 'a` does not imply `T: 'a`. We temporarily remove `shorter_region`
                // from all binders while we visit the type.
                let shorter_regions = self
                    .binders
                    .iter_mut()
                    .map(|binder| binder.shorter_region.take())
                    .collect_vec();
                let result = self.visit_inner(ty);
                for (binder, shorter) in self.binders.iter_mut().zip(shorter_regions) {
                    binder.shorter_region = shorter;
                }
                return result;
            }
            TyKind::Adt(type_ref) => {
                if let Some(decl) = self.type_decls.get(type_ref.id) {
                    let outlives = decl
                        .generics
                        .outlives
                        .iter()
                        .cloned()
                        .map(|pred| pred.substitute(&type_ref.generics))
                        .collect_vec();
                    for pred in outlives {
                        self.add_outlives(pred);
                    }
                }
            }
            _ => {}
        }
        match ty.kind() {
            TyKind::Ref(region @ (Region::Static | Region::Var(_) | Region::Lub(_)), _, _) => {
                self.with_shorter_region(region.clone(), |this| this.visit_inner(ty))
            }
            _ => self.visit_inner(ty),
        }
    }

    fn enter_region(&mut self, region: &mut Region) {
        if matches!(region, Region::Var(_) | Region::Lub(_)) {
            self.add_outliving_region(region);
        }
    }
}

struct ClosureOutlivesComputer<'a> {
    type_decls: &'a mut IndexMap<TypeDeclId, TypeDecl>,
    trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    /// Map of types we want to process.
    closure_tys: SeqHashMap<TypeDeclId, CycleDetector<()>>,
}

impl<'a> ClosureOutlivesComputer<'a> {
    fn new(
        type_decls: &'a mut IndexMap<TypeDeclId, TypeDecl>,
        trait_decls: &'a IndexMap<TraitDeclId, TraitDecl>,
    ) -> Self {
        let closure_tys = type_decls
            .iter()
            .filter(|decl| matches!(decl.src, TypeSource::Closure { .. }))
            .map(|decl| (decl.def_id, CycleDetector::Unprocessed))
            .collect();
        Self {
            type_decls,
            trait_decls,
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
                    if self.closure_tys.get(&type_ref.id).is_some() {
                        dependencies.push(type_ref.id);
                    }
                });
            for dependency in dependencies {
                self.compute(dependency);
            }

            // Move the kind out so that the crate can inspect the rest of the decls.
            let mut kind = mem::replace(&mut self.type_decls[type_id].kind, TypeDeclKind::Opaque);
            let mut params = mem::take(&mut self.type_decls[type_id].generics);
            let mut visitor = OutlivesGatherer::new(&mut params, self.type_decls, self.trait_decls);
            visitor.visit(&mut kind);
            visitor.finish();
            self.type_decls[type_id].generics = params;
            self.type_decls[type_id].kind = kind;
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
        let trait_decls = &mut ctx.translated.trait_decls;

        // Rustc gives us explicit outlives for ADTs, but we make fake ADTs for closures, so we
        // infer their outlives predicates here. Thankfully they can't be recursive, which makes
        // the implementation much easier than having to deal with all ADTs.
        ClosureOutlivesComputer::new(type_decls, trait_decls).compute_all();

        for fun_decl in &mut ctx.translated.fun_decls {
            let mut visitor =
                OutlivesGatherer::new(&mut fun_decl.generics, type_decls, trait_decls);
            visitor.visit(&mut fun_decl.signature);
            if let FunSource::InherentImpl { self_ty } = &mut fun_decl.src {
                // The inherent impl header contributes to the implied bounds even if that type is
                // not mentioned in the signature.
                visitor.visit(self_ty);
            }
            visitor.finish();

            // Also add implied bounds to the inner binders inside bodies. Implied bounds involving
            // only body or signature lifetimes must not be kept; they must be checked by
            // borrow-checking.
            OutlivesGatherer::new(&mut GenericParams::default(), type_decls, trait_decls)
                .visit(&mut fun_decl.body);
        }

        for timpl in &mut ctx.translated.trait_impls {
            let mut visitor = OutlivesGatherer::new(&mut timpl.generics, type_decls, trait_decls);
            visitor.visit(&mut timpl.impl_trait);
            visitor.finish();
        }

        for trait_id in trait_decls.iter_indices().collect_vec() {
            // Keep the associated type declarations available while visiting method signatures.
            let mut methods = mem::take(&mut trait_decls[trait_id].methods);
            for method in &mut methods {
                let mut visitor =
                    OutlivesGatherer::new(&mut method.params, type_decls, trait_decls);
                visitor.visit(&mut method.skip_binder.signature);
                visitor.finish();
            }
            trait_decls[trait_id].methods = methods;
        }
    }
}
