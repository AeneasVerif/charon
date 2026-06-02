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
use rustc_middle::ty::{self, *};
use rustc_span::def_id::DefId;
use rustc_span::{DUMMY_SP, Span};

use crate::{ElaborationCtx, ItemId, ToPolyTraitRef};

#[derive(Debug, Default, Clone)]
pub struct BoundsOptions {
    /// Add `T: Destruct` bounds to every type generic, so that we can build trait proofs to know
    /// what code is run on drop.
    pub add_destruct_bounds: bool,
    /// Traits to filter out from the predicate lists.
    pub remove_traits: HashSet<DefId>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum PredicateDirection {
    Required,
    Implied,
}

/// Uniquely identifies a predicate.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ItemPredicateId<Id = DefId> {
    /// A predicate that counts as "input" for an item, e.g. `where` clauses on a function or impl.
    /// Numbered in some arbitrary but consistent order.
    Required(Id, u32),
    /// A predicate that counts as "output" of an item, e.g. supertrait clauses in a trait. Note
    /// that we count `where` clauses on a trait as implied.
    /// Numbered in some arbitrary but consistent order.
    Implied(Id, u32),
    /// Predicate inside a non-item binder, e.g. within a `dyn Trait`.
    /// Numbered in some arbitrary but consistent order.
    Unmapped(u32),
    /// The special `Self: Trait` clause available within trait `Trait`.
    TraitSelf,
}

impl<Id> ItemPredicateId<Id> {
    fn new(def_id: Id, direction: PredicateDirection, next_id: &mut usize) -> Self {
        let i = *next_id as u32;
        *next_id += 1;
        match direction {
            PredicateDirection::Required => ItemPredicateId::Required(def_id, i),
            PredicateDirection::Implied => ItemPredicateId::Implied(def_id, i),
        }
    }
    fn new_unmapped(next_id: &mut usize) -> Self {
        let i = *next_id as u32;
        *next_id += 1;
        ItemPredicateId::Unmapped(i)
    }
}

#[derive(Debug, Clone)]
pub struct ItemPredicate<'tcx, Id = DefId> {
    pub id: ItemPredicateId<Id>,
    pub clause: Clause<'tcx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ItemPredicates<'tcx, Id = DefId> {
    direction: PredicateDirection,
    next_id: usize,
    pub predicates: Vec<ItemPredicate<'tcx, Id>>,
}

impl<'tcx, Id> Default for ItemPredicates<'tcx, Id> {
    fn default() -> Self {
        Self {
            direction: PredicateDirection::Implied,
            next_id: 0,
            predicates: Vec::new(),
        }
    }
}

impl<'tcx, Id: ItemId> ItemPredicates<'tcx, Id> {
    pub fn new(
        def_id: Id,
        direction: PredicateDirection,
        predicates: impl IntoIterator<Item = (Clause<'tcx>, Span)>,
    ) -> Self {
        let mut next_id = 0;
        let predicates = predicates
            .into_iter()
            .map(|(clause, span)| {
                let id = ItemPredicateId::new(def_id.clone(), direction, &mut next_id);
                ItemPredicate { id, clause, span }
            })
            .collect_vec();
        Self {
            next_id,
            direction,
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
            direction: PredicateDirection::Required,
            predicates,
        }
    }

    fn add_synthetic_predicates(
        &mut self,
        def_id: Id,
        predicates: impl IntoIterator<Item = Clause<'tcx>>,
    ) {
        self.predicates.extend(predicates.into_iter().map(|clause| {
            let id = ItemPredicateId::new(def_id.clone(), self.direction, &mut self.next_id);
            ItemPredicate {
                id,
                clause,
                span: DUMMY_SP,
            }
        }));
    }
    /// Add `T: Destruct` bounds for every generic parameter of the given item.
    fn add_destruct_bounds(&mut self, tcx: TyCtxt<'tcx>, state: &Id::State<'tcx>, def_id: Id)
    where
        Id: ItemId,
    {
        let destruct_trait = tcx.lang_items().destruct_trait().unwrap();
        let extra_bounds = def_id
            .generics_of(state)
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
    pub fn defined_on(
        tcx: TyCtxt<'tcx>,
        state: &Id::State<'tcx>,
        def_id: DefId,
        direction: PredicateDirection,
    ) -> Self {
        use DefKind::*;
        let id = Id::from_rust_def_id(state, def_id);
        let explicit_predicates_of = || {
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
            ItemPredicates::new(id.clone(), direction, predicates)
        };

        match tcx.def_kind(def_id) {
            AssocConst { .. }
            | AssocFn
            | AssocTy
            | Const { .. }
            | Enum
            | Fn
            | ForeignTy
            | Impl { .. }
            | OpaqueTy
            | Static { .. }
            | Struct
            | TyAlias
            | Union
                if direction == PredicateDirection::Required =>
            {
                explicit_predicates_of()
            }
            // We consider all predicates on traits to be outputs
            Trait | TraitAlias if direction == PredicateDirection::Implied => {
                explicit_predicates_of()
            }
            AssocTy
                if direction == PredicateDirection::Implied
                    && matches!(tcx.def_kind(tcx.parent(def_id)), DefKind::Trait) =>
            {
                ItemPredicates::new(
                    id,
                    PredicateDirection::Implied,
                    tcx.explicit_item_bounds(def_id)
                        .skip_binder()
                        .iter()
                        .copied(),
                )
            }
            // `explicit_predicates_of` ICEs on other def kinds.
            _ => Default::default(),
        }
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
        elab_ctx: ElaborationCtx<'tcx, Id>,
        state: &Id::State<'tcx>,
        def_id: Id,
    ) -> Self {
        elab_ctx.cached_required_predicates(def_id.clone(), || {
            let options = elab_ctx.bounds_options();
            let mut predicates = def_id.predicates_defined_on(state, PredicateDirection::Required);
            // For methods and assoc consts in trait definitions, we add an explicit `Self: Trait` clause.
            // Associated types get to use the implicit `Self: Trait` clause instead.
            if def_id.takes_explicit_self_clause(state)
                && let Some(parent) = def_id.parent_of_assoc(state)
                && let Some(self_clause) = parent.self_pred(state)
            {
                predicates.predicates.insert(
                    0,
                    ItemPredicate {
                        id: ItemPredicateId::TraitSelf,
                        clause: self_clause.upcast(elab_ctx.tcx),
                        span: DUMMY_SP,
                    },
                );
            }
            let is_trait = def_id.self_pred(state).is_some();
            // Add a `T: Destruct` bound for every generic. For traits we consider these predicates
            // implied instead of required.
            if options.add_destruct_bounds && !is_trait {
                // Closures and inline consts have fictitious weird type parameters in their
                // `own_args` that we don't want to add `Destruct` bounds for.
                if def_id.typeck_parent(state).is_none() {
                    predicates.add_destruct_bounds(elab_ctx.tcx, state, def_id.clone());
                }
            }
            predicates.filter_traits(options);
            predicates
        })
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
        elab_ctx: ElaborationCtx<'tcx, Id>,
        state: &Id::State<'tcx>,
        def_id: Id,
    ) -> Self {
        elab_ctx.cached_required_recursively_predicates(def_id.clone(), || {
            fn acc_predicates<'tcx, Id: ItemId>(
                elab_ctx: ElaborationCtx<'tcx, Id>,
                state: &Id::State<'tcx>,
                def_id: Id,
                predicates: &mut ItemPredicates<'tcx, Id>,
                is_parent: bool,
            ) {
                if let Some(parent) = def_id.parent_for_clauses(state) {
                    acc_predicates(elab_ctx, state, parent, predicates, true);
                }
                let required = ItemPredicates::required(elab_ctx, state, def_id);
                predicates.predicates.extend(required.iter());
                if !is_parent {
                    // Use the next_id that corresponds to the current item.
                    predicates.next_id = required.next_id;
                }
            }

            let mut predicates = Self {
                direction: PredicateDirection::Required,
                next_id: 0,
                predicates: vec![],
            };
            acc_predicates(elab_ctx, state, def_id, &mut predicates, false);
            predicates
        })
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
        elab_ctx: ElaborationCtx<'tcx, Id>,
        state: &Id::State<'tcx>,
        def_id: Id,
    ) -> Self {
        elab_ctx.cached_implied_predicates(def_id.clone(), || {
            let tcx = elab_ctx.tcx;
            let options = elab_ctx.bounds_options();
            let mut predicates = def_id.predicates_defined_on(state, PredicateDirection::Implied);
            if options.add_destruct_bounds {
                if let Some(pred) = def_id.self_pred(state) {
                    // Add a `T: Drop` bound for every generic, unless the current trait is `Drop` itself, or a
                    // built-in marker trait that we know doesn't need the bound.
                    if !matches!(
                        tcx.as_lang_item(pred.def_id()),
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
                        predicates.add_destruct_bounds(tcx, state, def_id.clone());
                    }
                } else if let Some(ty) = def_id.as_identity_assoc_ty(state) {
                    // Add a `Destruct` bound to the associated type itself.
                    let destruct_trait = tcx.lang_items().destruct_trait().unwrap();
                    let tref = Binder::dummy(TraitRef::new(tcx, destruct_trait, [ty]));
                    predicates.add_synthetic_predicates(def_id.clone(), [tref.upcast(tcx)]);
                };
            }
            predicates.filter_traits(options);
            predicates
        })
    }
}

impl<'tcx, Id: Clone> ItemPredicates<'tcx, Id> {
    pub fn len(&self) -> usize {
        self.predicates.len()
    }
    pub fn iter(&self) -> impl Iterator<Item = ItemPredicate<'tcx, Id>> + '_ {
        self.predicates.iter().cloned()
    }
    pub fn iter_trait_clauses(
        &self,
    ) -> impl Iterator<Item = (ItemPredicateId<Id>, PolyTraitRef<'tcx>)> + '_ {
        self.iter().filter_map(|pred| {
            let tref = pred.clause.as_trait_clause()?.to_poly_trait_ref();
            Some((pred.id, tref))
        })
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut ItemPredicate<'tcx, Id>> {
        self.predicates.iter_mut()
    }

    /// Substitute all the predicates with these args.
    pub fn instantiate(mut self, tcx: TyCtxt<'tcx>, args: ty::GenericArgsRef<'tcx>) -> Self {
        for predicate in self.iter_mut() {
            predicate.clause = ty::EarlyBinder::bind(predicate.clause)
                .instantiate(tcx, args)
                .skip_norm_wip();
        }
        self
    }
}

/// The special "self" predicate on a trait.
pub fn self_predicate<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> PolyTraitRef<'tcx> {
    // Copied from the code of `tcx.predicates_of()`.
    Binder::dummy(TraitRef::identity(tcx, def_id))
}

pub fn inherits_parent_clauses<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    use DefKind::*;
    matches!(
        tcx.def_kind(def_id),
        AnonConst
            | AssocConst { .. }
            | AssocFn
            | AssocTy
            | Closure
            | Ctor(..)
            | InlineConst
            | Variant
    )
}
