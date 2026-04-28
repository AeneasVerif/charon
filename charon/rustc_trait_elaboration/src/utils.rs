//! Each item can involve three kinds of predicates:
//! - input aka required predicates: the predicates required to mention the item. These are usually `where`
//!   clauses (or equivalent) on the item:
//! ```ignore
//! struct Foo<T: Clone> { ... }
//! trait Foo<T> where T: Clone { ... }
//! fn function<I>() where I: Iterator, I::Item: Clone { ... }
//! ```
//! - output aka implied predicates: the predicates that are implied by the presence of this item in a
//!   signature. This is mostly trait parent predicates:
//! ```ignore
//! trait Foo: Clone { ... }
//! fn bar<T: Foo>() {
//!   // from `T: Foo` we can deduce `T: Clone`
//! }
//! ```
//!   This could also include implied predicates such as `&'a T` implying `T: 'a` but we don't
//!   consider these.
//! - "self" predicate: that's the special `Self: Trait` predicate in scope within a trait
//!   declaration or implementation for trait `Trait`.
//!
//! Note that within a given item the polarity is reversed: input predicates are the ones that can
//! be assumed to hold and output predicates must be proven to hold. The "self" predicate is both
//! assumed and proven within an impl block, and just assumed within a trait declaration block.
//!
//! The current implementation considers all predicates on traits to be outputs, which has the
//! benefit of reducing the size of signatures. Moreover, the rules on which bounds are required vs
//! implied are subtle. We may change this if this proves to be a problem.
use rustc_middle::ty::*;

/// Normalize a value.
pub fn normalize<'tcx, T>(tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>, value: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>> + Clone,
{
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_middle::traits::ObligationCause;
    use rustc_trait_selection::traits::query::normalize::QueryNormalizeExt;
    let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
    infcx
        .at(&ObligationCause::dummy(), param_env)
        .query_normalize(value.clone())
        // We ignore the generated outlives relations. Unsure what we should do with them.
        .map(|x| x.value)
        .unwrap_or(value)
}

/// Erase free regions from the given value. Largely copied from `tcx.erase_and_anonymize_regions`, but also
/// erases bound regions that are bound outside `value`, so we can call this function inside a
/// `Binder`.
pub fn erase_free_regions<'tcx, T>(tcx: TyCtxt<'tcx>, value: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>>,
{
    use rustc_middle::ty;
    struct RegionEraserVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
        depth: u32,
    }

    impl<'tcx> TypeFolder<TyCtxt<'tcx>> for RegionEraserVisitor<'tcx> {
        fn cx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
            ty.super_fold_with(self)
        }

        fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
        where
            T: TypeFoldable<TyCtxt<'tcx>>,
        {
            let t = self.tcx.anonymize_bound_vars(t);
            self.depth += 1;
            let t = t.super_fold_with(self);
            self.depth -= 1;
            t
        }

        fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
            // We don't erase bound regions that are bound inside the expression we started with,
            // but we do erase those that point "outside of it".
            match r.kind() {
                ty::ReBound(BoundVarIndexKind::Bound(dbid), _) if dbid.as_u32() < self.depth => r,
                _ => self.tcx.lifetimes.re_erased,
            }
        }
    }
    value.fold_with(&mut RegionEraserVisitor { tcx, depth: 0 })
}

// Normalize and erase lifetimes, erasing more lifetimes than normal because we might be already
// inside a binder and rustc doesn't like that.
pub fn erase_and_norm<'tcx, T>(tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>, x: T) -> T
where
    T: TypeFoldable<TyCtxt<'tcx>> + Copy,
{
    erase_free_regions(
        tcx,
        tcx.try_normalize_erasing_regions(typing_env, x)
            .unwrap_or(x),
    )
}

/// Given our currently hacky handling of binders, in order for trait resolution to work we must
/// empty out the binders of trait refs. Specifically it's so that we can reconnect associated type
/// constraints with the trait ref they come from, given that the projection in question doesn't
/// track the right binder currently.
pub fn normalize_bound_val<'tcx, T>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    x: Binder<'tcx, T>,
) -> Binder<'tcx, T>
where
    T: TypeFoldable<TyCtxt<'tcx>> + Copy,
{
    Binder::dummy(erase_and_norm(tcx, typing_env, x.skip_binder()))
}

pub trait ToPolyTraitRef<'tcx> {
    fn to_poly_trait_ref(&self) -> PolyTraitRef<'tcx>;
}

impl<'tcx> ToPolyTraitRef<'tcx> for PolyTraitPredicate<'tcx> {
    fn to_poly_trait_ref(&self) -> PolyTraitRef<'tcx> {
        self.map_bound_ref(|trait_pred| trait_pred.trait_ref)
    }
}
