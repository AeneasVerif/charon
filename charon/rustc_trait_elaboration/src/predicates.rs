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
//! benefit of reducing the size of signatures. Moreover, the rustc rules on which bounds are
//! required vs implied are subtle. We may change our choice if this proves to be a problem.
use itertools::Itertools;
use std::collections::HashSet;

use rustc_hir::LangItem;
use rustc_hir::def::DefKind;
use rustc_middle::ty::*;
use rustc_span::def_id::DefId;
use rustc_span::{DUMMY_SP, Span};

use crate::ToPolyTraitRef;

#[derive(Debug, Default, Clone)]
pub struct BoundsOptions {
    /// Add `T: Destruct` bounds to every type generic, so that we can build `ImplExpr`s to know
    /// what code is run on drop.
    pub add_destruct_bounds: bool,
    /// Traits to filter out from the predicate lists.
    pub remove_traits: HashSet<DefId>,
}

/// Uniquely identifies a predicate.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ItemPredicateId {
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

impl ItemPredicateId {
    fn new(def_id: DefId, required: bool, next_id: &mut usize) -> Self {
        let i = *next_id as u32;
        *next_id += 1;
        if required {
            ItemPredicateId::Required(def_id, i)
        } else {
            ItemPredicateId::Implied(def_id, i)
        }
    }
    fn new_unmapped(next_id: &mut usize) -> Self {
        let i = *next_id as u32;
        *next_id += 1;
        ItemPredicateId::Unmapped(i)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ItemPredicate<'tcx> {
    pub id: ItemPredicateId,
    pub clause: Clause<'tcx>,
    pub span: Span,
}

#[derive(Debug, Default, Clone)]
pub struct ItemPredicates<'tcx> {
    required: bool,
    next_id: usize,
    pub predicates: Vec<ItemPredicate<'tcx>>,
}

impl<'tcx> ItemPredicates<'tcx> {
    fn new(
        def_id: DefId,
        required: bool,
        predicates: impl IntoIterator<Item = (Clause<'tcx>, Span)>,
    ) -> Self {
        let mut next_id = 0;
        let predicates = predicates
            .into_iter()
            .map(|(clause, span)| {
                let id = ItemPredicateId::new(def_id, required, &mut next_id);
                ItemPredicate { id, clause, span }
            })
            .collect_vec();
        Self {
            next_id,
            required,
            predicates,
        }
    }
    pub fn new_unmapped(span: Span, predicates: impl IntoIterator<Item = Clause<'tcx>>) -> Self {
        let mut next_id = 0;
        let predicates = predicates
            .into_iter()
            .map(|clause| {
                let id = ItemPredicateId::new_unmapped(&mut next_id);
                ItemPredicate { id, clause, span }
            })
            .collect_vec();
        Self {
            next_id,
            required: true,
            predicates,
        }
    }

    fn add_synthetic_predicates(
        &mut self,
        def_id: DefId,
        predicates: impl IntoIterator<Item = Clause<'tcx>>,
    ) {
        self.predicates.extend(predicates.into_iter().map(|clause| {
            let id = ItemPredicateId::new(def_id, self.required, &mut self.next_id);
            ItemPredicate {
                id,
                clause,
                span: DUMMY_SP,
            }
        }));
    }
    /// Add `T: Destruct` bounds for every generic parameter of the given item.
    fn add_destruct_bounds(&mut self, tcx: TyCtxt<'tcx>, def_id: DefId) {
        let def_kind = tcx.def_kind(def_id);
        if matches!(def_kind, DefKind::Closure | DefKind::InlineConst) {
            // Closures and inline consts have fictitious weird type parameters in their `own_args`
            // that we don't want to add `Destruct` bounds for.
            return;
        }
        // Add a `T: Destruct` bound for every generic.
        let destruct_trait = tcx.lang_items().destruct_trait().unwrap();
        let extra_bounds = tcx
            .generics_of(def_id)
            .own_params
            .iter()
            .filter(|param| matches!(param.kind, GenericParamDefKind::Type { .. }))
            .map(|param| tcx.mk_param_from_def(param))
            .map(|ty| Binder::dummy(TraitRef::new(tcx, destruct_trait, [ty])))
            .map(|tref| tref.upcast(tcx));
        self.add_synthetic_predicates(def_id, extra_bounds);
    }
    /// Remove the traits specified in `options`.
    fn filter_traits(&mut self, options: &BoundsOptions) {
        if !options.remove_traits.is_empty() {
            self.predicates.retain(|pred| {
                pred.clause.as_trait_clause().is_none_or(|trait_predicate| {
                    !options
                        .remove_traits
                        .contains(&trait_predicate.skip_binder().def_id())
                })
            });
        }
    }

    /// Returns a list of type predicates for the definition with id `def_id`, including inferred
    /// lifetime constraints. This is the basic list of predicates we use for essentially all
    /// items.
    pub fn defined_on(tcx: TyCtxt<'_>, def_id: DefId, required: bool) -> ItemPredicates<'_> {
        let predicates = tcx
            .explicit_predicates_of(def_id)
            .predicates
            .iter()
            .copied()
            .chain(
                tcx.inferred_outlives_of(def_id)
                    .iter()
                    .copied()
                    .map(|(clause, span)| (clause.upcast(tcx), span)),
            );
        ItemPredicates::new(def_id, required, predicates)
    }
    /// The predicates that must hold to mention this item (ignoring its parents). E.g.
    ///
    /// ```ignore
    /// // `U: OtherTrait` is required, `Self: Sized` is implied.
    /// trait Trait<U: OtherTrait>: Sized {
    ///     // `T: Clone` is required, `Self::Type<T>: Debug` is implied.
    ///     type Type<T: Clone>: Debug;
    /// }
    /// ```
    ///
    /// If `add_drop` is true, we add a `T: Drop` bound for every type generic.
    pub fn required(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        options: &BoundsOptions,
    ) -> ItemPredicates<'tcx> {
        use DefKind::*;
        let def_kind = tcx.def_kind(def_id);
        let mut predicates = match def_kind {
            AssocConst
            | AssocFn
            | AssocTy
            | Const
            | Enum
            | Fn
            | ForeignTy
            | Impl { .. }
            | OpaqueTy
            | Static { .. }
            | Struct
            | TyAlias
            | Union => Self::defined_on(tcx, def_id, true),
            // We consider all predicates on traits to be outputs
            Trait | TraitAlias => Default::default(),
            // `predicates_defined_on` ICEs on other def kinds.
            _ => Default::default(),
        };
        // For methods and assoc consts in trait definitions, we add an explicit `Self: Trait` clause.
        // Associated types get to use the implicit `Self: Trait` clause instead.
        if !matches!(def_kind, AssocTy)
            && let Some(trait_def_id) = tcx.trait_of_assoc(def_id)
        {
            let self_clause = self_predicate(tcx, trait_def_id).upcast(tcx);
            predicates.predicates.insert(
                0,
                ItemPredicate {
                    id: ItemPredicateId::TraitSelf,
                    clause: self_clause,
                    span: DUMMY_SP,
                },
            );
        }
        if options.add_destruct_bounds && !matches!(def_kind, Trait | TraitAlias) {
            // Add a `T: Destruct` bound for every generic. For traits we consider these predicates
            // implied instead of required.
            predicates.add_destruct_bounds(tcx, def_id);
        }
        predicates.filter_traits(options);
        predicates
    }
    /// The predicates that must hold to mention this item, including its parents. E.g.
    ///
    /// ```ignore
    /// // `U: OtherTrait` is required.
    /// trait Trait<U: OtherTrait> {
    ///     // `U: OtherTrait` and `T: Clone` are required.
    ///     type Type<T: Clone>;
    /// }
    /// ```
    pub fn required_recursively(
        tcx: TyCtxt<'tcx>,
        def_id: rustc_span::def_id::DefId,
        options: &BoundsOptions,
    ) -> ItemPredicates<'tcx> {
        fn acc_predicates<'tcx>(
            tcx: TyCtxt<'tcx>,
            def_id: rustc_span::def_id::DefId,
            options: &BoundsOptions,
            predicates: &mut ItemPredicates<'tcx>,
            is_parent: bool,
        ) {
            if inherits_parent_clauses(tcx, def_id) {
                let parent = tcx.parent(def_id);
                acc_predicates(tcx, parent, options, predicates, true);
            }
            let required = ItemPredicates::required(tcx, def_id, options);
            predicates.predicates.extend(required.iter());
            if !is_parent {
                // Use the next_id that corresponds to the current item.
                predicates.next_id = required.next_id;
            }
        }

        let mut predicates = Self {
            required: true,
            next_id: 0,
            predicates: vec![],
        };
        acc_predicates(tcx, def_id, options, &mut predicates, false);
        predicates
    }
    /// The predicates that can be deduced from the presence of this item in a signature. We only
    /// consider predicates implied by traits here, not implied bounds such as `&'a T` implying `T:
    /// 'a`. E.g.
    ///
    /// ```ignore
    /// // `U: OtherTrait` is required, `Self: Sized` is implied.
    /// trait Trait<U: OtherTrait>: Sized {
    ///     // `T: Clone` is required, `Self::Type<T>: Debug` is implied.
    ///     type Type<T: Clone>: Debug;
    /// }
    /// ```
    ///
    /// If `add_drop` is true, we add a `T: Drop` bound for every type generic and associated type.
    pub fn implied(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        options: &BoundsOptions,
    ) -> ItemPredicates<'tcx> {
        use DefKind::*;
        let parent = tcx.opt_parent(def_id);
        let mut predicates = match tcx.def_kind(def_id) {
            // We consider all predicates on traits to be outputs
            Trait | TraitAlias => {
                let mut predicates = Self::defined_on(tcx, def_id, false);
                if options.add_destruct_bounds {
                    // Add a `T: Drop` bound for every generic, unless the current trait is `Drop` itself, or a
                    // built-in marker trait that we know doesn't need the bound.
                    if !matches!(
                        tcx.as_lang_item(def_id),
                        Some(
                            LangItem::Destruct
                                | LangItem::Sized
                                | LangItem::MetaSized
                                | LangItem::PointeeSized
                                | LangItem::DiscriminantKind
                                | LangItem::PointeeTrait
                                | LangItem::Tuple
                        )
                    ) {
                        predicates.add_destruct_bounds(tcx, def_id);
                    }
                }
                predicates
            }
            AssocTy if matches!(tcx.def_kind(parent.unwrap()), Trait) => {
                // `skip_binder` is for the GAT `EarlyBinder`
                let mut predicates = ItemPredicates::new(
                    def_id,
                    false,
                    tcx.explicit_item_bounds(def_id)
                        .skip_binder()
                        .iter()
                        .copied(),
                );
                if options.add_destruct_bounds {
                    // Add a `Drop` bound to the assoc item.
                    let destruct_trait = tcx.lang_items().destruct_trait().unwrap();
                    let ty = Ty::new_projection(
                        tcx,
                        def_id,
                        GenericArgs::identity_for_item(tcx, def_id),
                    );
                    let tref = Binder::dummy(TraitRef::new(tcx, destruct_trait, [ty]));
                    predicates.add_synthetic_predicates(def_id, [tref.upcast(tcx)]);
                }
                predicates
            }
            _ => ItemPredicates::default(),
        };
        predicates.filter_traits(options);
        predicates
    }

    pub fn len(&self) -> usize {
        self.predicates.len()
    }
    pub fn iter(&self) -> impl Iterator<Item = ItemPredicate<'tcx>> {
        self.predicates.iter().copied()
    }
    pub fn iter_trait_clauses(
        &self,
    ) -> impl Iterator<Item = (ItemPredicateId, PolyTraitRef<'tcx>)> {
        self.iter().filter_map(|pred| {
            let tref = pred.clause.as_trait_clause()?.to_poly_trait_ref();
            Some((pred.id, tref))
        })
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut ItemPredicate<'tcx>> {
        self.predicates.iter_mut()
    }
}

/// The special "self" predicate on a trait.
pub fn self_predicate<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> PolyTraitRef<'tcx> {
    // Copied from the code of `tcx.predicates_of()`.
    Binder::dummy(TraitRef::identity(tcx, def_id))
}

fn inherits_parent_clauses<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    use DefKind::*;
    matches!(
        tcx.def_kind(def_id),
        AnonConst | AssocConst | AssocFn | AssocTy | Closure | Ctor(..) | InlineConst | Variant
    )
}
