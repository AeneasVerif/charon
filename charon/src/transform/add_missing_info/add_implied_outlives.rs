//! Make explicit the outlives predicates implied by item signatures.
use derive_generic_visitor::*;
use itertools::Itertools;
use std::hash::Hash;
use std::mem;

use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};
use crate::utils::CycleDetector;

type BoundRegionOutlives = RegionBinder<RegionOutlives>;
type BoundTypeOutlives = RegionBinder<TypeOutlives>;

#[derive(Default)]
struct OutlivesAtBinder {
    regions_outlive: SeqHashSet<BoundRegionOutlives>,
    types_outlive: SeqHashSet<BoundTypeOutlives>,
    /// The lifetime of the innermost reference we're inside of. When going under a binder, we keep
    /// it there.
    ///
    /// E.g. in `&'a for<'b> fn(&'b u32, &'c u32)`, the `'a` stays on the outer binder, and we use
    /// that to add `'c: 'a` but we don't add `'b: 'a` since `'b` is not visible from where `'a`
    /// is.
    shorter_region: Option<Region>,
}

impl OutlivesAtBinder {
    fn finish(
        self,
        regions_outlive: &mut Vec<BoundRegionOutlives>,
        types_outlive: &mut Vec<BoundTypeOutlives>,
    ) {
        debug_assert!(self.shorter_region.is_none());
        let mut regions: SeqHashSet<_> = mem::take(regions_outlive).into_iter().collect();
        regions.extend(self.regions_outlive);
        regions_outlive.extend(regions.into_iter().filter(|pred| {
            let OutlivesPred(longer, shorter) = pred.skip_binder;
            longer != shorter && longer != Region::Erased && shorter != Region::Erased
        }));
        let mut types: SeqHashSet<_> = mem::take(types_outlive).into_iter().collect();
        types.extend(self.types_outlive);
        types_outlive.extend(types.into_iter().filter(|pred| {
            let OutlivesPred(_, shorter) = pred.skip_binder;
            shorter != Region::Erased
        }));
    }
}

/// Explore a type and accumulate the outlives predicates it implies.
#[derive(Visitor)]
struct OutlivesGatherer<'a> {
    type_decls: &'a IndexMap<TypeDeclId, TypeDecl>,
    item_params: &'a mut GenericParams,
    binders: BindingStack<OutlivesAtBinder>,
}

impl<'a> OutlivesGatherer<'a> {
    fn new(
        item_params: &'a mut GenericParams,
        type_decls: &'a IndexMap<TypeDeclId, TypeDecl>,
    ) -> Self {
        Self {
            type_decls,
            item_params,
            binders: BindingStack::new(OutlivesAtBinder::default()),
        }
    }

    fn finish(mut self) {
        let outlives = self.binders.pop().unwrap();
        debug_assert!(self.binders.is_empty());
        outlives.finish(
            &mut self.item_params.regions_outlive,
            &mut self.item_params.types_outlive,
        );
    }

    fn add_region_outlives(&mut self, pred: BoundRegionOutlives) {
        let (pred, level) = self.binders.place_at_outermost(&pred);
        level.regions_outlive.insert(pred);
    }
    fn add_type_outlives(&mut self, pred: BoundTypeOutlives) {
        let (pred, level) = self.binders.place_at_outermost(&pred);
        level.types_outlive.insert(pred);
    }

    fn add_outliving_region(&mut self, longer: Region) {
        self.add_outliving(&longer, |outlives| &mut outlives.regions_outlive);
    }
    fn add_outliving_type(&mut self, longer: &Ty) {
        self.add_outliving(longer, |outlives| &mut outlives.types_outlive);
    }
    fn add_outliving<T>(
        &mut self,
        longer: &T,
        mut get: impl FnMut(
            &mut OutlivesAtBinder,
        ) -> &mut SeqHashSet<RegionBinder<OutlivesPred<T, Region>>>,
    ) where
        T: TyVisitable + Clone + Eq + Hash,
    {
        // Find the innermost region that affects `longer`: it needs to be bound at a level where
        // `longer` can be moved to.
        let Some((bound_depth, pred)) =
            self.binders.iter_enumerated().find_map(|(depth, binder)| {
                let shorter = binder.shorter_region?;
                let longer = longer.clone().move_from_under_binders(depth)?;
                let pred = RegionBinder::empty(OutlivesPred(longer, shorter));
                Some((depth, pred))
            })
        else {
            return;
        };
        // Place the predicate at the outermost level.
        let (pred, level) = self.binders[bound_depth..].place_at_outermost(&pred);
        get(level).insert(pred);
    }

    fn with_shorter_region(
        &mut self,
        region: Region,
        f: impl FnOnce(&mut Self) -> ControlFlow<Infallible>,
    ) -> ControlFlow<Infallible> {
        self.add_outliving_region(region);
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
        self.binders.pop().unwrap().finish(
            &mut binder.params.regions_outlive,
            &mut binder.params.types_outlive,
        );
        result
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        binder: &mut RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        self.binders.push(OutlivesAtBinder::default());
        let result = self.visit_inner(binder);
        self.binders
            .pop()
            .unwrap()
            .finish(&mut binder.regions_outlive, &mut binder.types_outlive);
        result
    }

    fn visit_ty(&mut self, ty: &mut Ty) -> ControlFlow<Self::Break> {
        match ty.kind() {
            TyKind::TypeVar(_) | TyKind::TraitType(..) => {
                self.add_outliving_type(ty);
            }
            TyKind::Adt(type_ref) => {
                if let Some(decl) = self.type_decls.get(type_ref.id) {
                    let regions_outlive = decl
                        .generics
                        .regions_outlive
                        .iter()
                        .cloned()
                        .map(|pred| pred.substitute(&type_ref.generics))
                        .collect_vec();
                    let types_outlive = decl
                        .generics
                        .types_outlive
                        .iter()
                        .cloned()
                        .map(|pred| pred.substitute(&type_ref.generics))
                        .collect_vec();
                    for pred in regions_outlive {
                        self.add_region_outlives(pred);
                    }
                    for pred in types_outlive {
                        self.add_type_outlives(pred);
                    }
                }
            }
            _ => {}
        }
        match ty.kind() {
            TyKind::Ref(region @ (Region::Static | Region::Var(_)), _, _) => {
                self.with_shorter_region(*region, |this| this.visit_inner(ty))
            }
            _ => self.visit_inner(ty),
        }
    }

    fn enter_region(&mut self, region: &mut Region) {
        if let longer @ Region::Var(_) = *region {
            self.add_outliving_region(longer);
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
            let mut visitor = OutlivesGatherer::new(&mut params, self.type_decls);
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

        // Rustc gives us explicit outlives for ADTs, but we make fake ADTs for closures, so we
        // infer their outlives predicates here. Thankfully they can't be recursive, which makes
        // the implementation much easier than having to deal with all ADTs.
        ClosureOutlivesComputer::new(type_decls).compute_all();

        for fun_decl in &mut ctx.translated.fun_decls {
            let mut visitor = OutlivesGatherer::new(&mut fun_decl.generics, type_decls);
            visitor.visit(&mut fun_decl.signature);
            visitor.finish();
        }

        for timpl in &mut ctx.translated.trait_impls {
            let mut visitor = OutlivesGatherer::new(&mut timpl.generics, type_decls);
            visitor.visit(&mut timpl.impl_trait);
            visitor.finish();
        }
    }
}
