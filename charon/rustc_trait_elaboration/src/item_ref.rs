use std::{fmt::Debug, hash::Hash, ops::Deref, sync::Arc};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, GenericArg, GenericArgsRef};

use crate::{
    DYN_SELF_PARAM_INDEX, ItemPredicates, PredicateDirection, PredicateSearcher, TraitProof,
    TraitProofKind, inherits_parent_clauses, normalize, self_predicate,
};

/// The identifier of an item; generalizes over rustc's `DefId` to allow for virtual items.
pub trait ItemId: Clone + Debug + Hash + PartialEq + Eq {
    /// State needed to query information about this item.
    type State<'tcx>: ?Sized;

    /// An identifier that refers to a real Rust item.
    fn from_rust_def_id<'tcx>(state: &Self::State<'tcx>, def_id: DefId) -> Self;

    /// The generics of this item.
    fn generics_of<'tcx>(&self, state: &Self::State<'tcx>) -> &'tcx ty::Generics;

    /// The clauses that can be assumed when inside this item.
    fn param_env<'tcx>(&self, state: &Self::State<'tcx>) -> ty::ParamEnv<'tcx>;

    /// The predicates defined directly on this item.
    fn predicates_defined_on<'tcx>(
        &self,
        state: &Self::State<'tcx>,
        direction: PredicateDirection,
    ) -> ItemPredicates<'tcx, Self>;

    /// If this item is a trait, return its Self predicate.
    fn self_pred<'tcx>(&self, state: &Self::State<'tcx>) -> Option<ty::PolyTraitRef<'tcx>>;

    /// The type of this item as an associated type projection, if it is a trait associated type.
    fn as_identity_assoc_ty<'tcx>(&self, state: &Self::State<'tcx>) -> Option<ty::Ty<'tcx>>;

    /// If this item is typechecked together with its parent (e.g. inline consts and closures),
    /// return that parent.
    fn typeck_parent<'tcx>(&self, state: &Self::State<'tcx>) -> Option<Self>;

    /// If this item inherits the clauses of its parent, return the parent.
    fn parent_for_clauses<'tcx>(&self, state: &Self::State<'tcx>) -> Option<Self>;

    /// If this item is an associated item, return its parent.
    fn parent_of_assoc<'tcx>(&self, state: &Self::State<'tcx>) -> Option<Self>;

    /// Whether this item takes an explicit `Self: Trait` clause or whether it is allowed to refer
    /// to the ambiant one. Only relevant for associated items.
    fn takes_explicit_self_clause<'tcx>(&self, state: &Self::State<'tcx>) -> bool;

    /// If this item is an associated item definition, and the given impl implements it, returns
    /// the implemented associated item.
    fn find_in_impl<'tcx>(&self, state: &Self::State<'tcx>, trait_impl: &Self) -> Option<Self>;
}

impl ItemId for DefId {
    type State<'tcx> = ty::TyCtxt<'tcx>;

    fn from_rust_def_id<'tcx>(_: &Self::State<'tcx>, def_id: DefId) -> Self {
        def_id
    }

    fn generics_of<'tcx>(&self, tcx: &Self::State<'tcx>) -> &'tcx ty::Generics {
        tcx.generics_of(*self)
    }

    fn param_env<'tcx>(&self, tcx: &Self::State<'tcx>) -> ty::ParamEnv<'tcx> {
        tcx.param_env(*self)
    }

    fn predicates_defined_on<'tcx>(
        &self,
        tcx: &Self::State<'tcx>,
        direction: PredicateDirection,
    ) -> ItemPredicates<'tcx, Self> {
        ItemPredicates::defined_on(*tcx, tcx, *self, direction)
    }

    fn self_pred<'tcx>(&self, tcx: &Self::State<'tcx>) -> Option<ty::PolyTraitRef<'tcx>> {
        match tcx.def_kind(*self) {
            DefKind::Trait | DefKind::TraitAlias => Some(self_predicate(*tcx, *self)),
            _ => None,
        }
    }

    fn as_identity_assoc_ty<'tcx>(&self, tcx: &Self::State<'tcx>) -> Option<ty::Ty<'tcx>> {
        (matches!(tcx.def_kind(*self), DefKind::AssocTy)
            && matches!(tcx.def_kind(tcx.parent(*self)), DefKind::Trait))
        .then(|| {
            ty::Ty::new_projection(
                *tcx,
                ty::IsRigid::No,
                *self,
                ty::GenericArgs::identity_for_item(*tcx, *self),
            )
        })
    }

    fn typeck_parent<'tcx>(&self, tcx: &Self::State<'tcx>) -> Option<Self> {
        tcx.is_typeck_child(*self)
            .then(|| tcx.typeck_root_def_id(*self))
    }

    fn parent_of_assoc<'tcx>(&self, tcx: &Self::State<'tcx>) -> Option<Self> {
        tcx.def_kind(*self).is_assoc().then(|| tcx.parent(*self))
    }

    fn parent_for_clauses<'tcx>(&self, tcx: &Self::State<'tcx>) -> Option<Self> {
        inherits_parent_clauses(*tcx, *self).then(|| tcx.parent(*self))
    }

    fn takes_explicit_self_clause<'tcx>(&self, tcx: &Self::State<'tcx>) -> bool {
        matches!(tcx.def_kind(*self), DefKind::AssocFn | DefKind::AssocConst)
    }

    fn find_in_impl<'tcx>(&self, tcx: &Self::State<'tcx>, trait_impl: &Self) -> Option<Self> {
        tcx.associated_items(*trait_impl)
            .in_definition_order()
            .find(|item| item.trait_item_def_id() == Some(*self))
            .map(|item| item.def_id)
    }
}

/// Reference to an item, with generics as well as trait proofs for the required predicates.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ItemRef<'tcx, Id: ItemId = DefId> {
    // TODO: intern?
    contents: Arc<ItemRefContents<'tcx, Id>>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ItemRefContents<'tcx, Id: ItemId = DefId> {
    /// The item being refered to.
    pub def_id: Id,
    /// The arguments provided to this item.
    pub generic_args: ty::GenericArgsRef<'tcx>,
    /// The number of generic arguments excluding the extra inference arguments of closures and
    /// inline consts.
    pub proper_arg_count: usize,
    /// If we're referring to a trait associated item, this gives the trait clause/impl we're
    /// referring to, as well as the number of clauses required to mention the trait (cached for
    /// easy access).
    pub in_trait: Option<(TraitProof<'tcx, Id>, usize)>,
    /// Whether this item is an associated item that takes an explicit `Self: Trait` clause.
    pub needs_explicit_self_clause: bool,
    /// Whether this contains any reference to a type/lifetime/const parameter.
    pub has_param: bool,
    /// Whether this mentions the generic parameters of the item under which the reference was made.
    /// If `false`, the trait proofs for this reference don't depend on the owner.
    pub has_owner_param: bool,
    /// Whether this contains any reference to a type/const parameter.
    pub has_non_lt_param: bool,
}

impl<'tcx, Id: ItemId> ItemRefContents<'tcx, Id> {
    fn intern(self) -> ItemRef<'tcx, Id> {
        ItemRef {
            contents: Arc::new(self),
        }
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum AssocItemResolution {
    /// Leave trait associated items as plain item references.
    None,
    /// Resolve the trait proof of a trait associated item, but keep the trait item id.
    TraitProof,
    /// Resolve the trait proof and, when possible, point to the concrete impl item.
    ImplItem,
}

impl<'tcx, Id: ItemId> PredicateSearcher<'tcx, Id> {
    /// Construct an `ItemRef` by filling in the trait proofs required to mention said item.
    ///
    /// If `resolve_assoc_item_trait_ref == true` and `(def_id, generics)` points to a trait
    /// associated item that can be resolved to a specific `impl`, `translate` rewrites `def_id` to
    /// the concrete associated item from that `impl` and rebases the generics.
    ///
    /// For instance, `<u32 as From<u8>>::from` produces a [`ItemRef`] with a [`DefId`] looking
    /// like `core::convert::num::Impl#42::from` when `resolve_impl` is `true`, otherwise keeps the
    /// `DefId` of the trait item definition: `core::convert::From::from`.
    pub fn resolve_item_reference(
        &mut self,
        state: &Id::State<'tcx>,
        def_id: Id,
        generics: ty::GenericArgsRef<'tcx>,
        assoc_item_resolution: AssocItemResolution,
    ) -> ItemRef<'tcx, Id> {
        let key = (def_id.clone(), generics, assoc_item_resolution);
        if let Some(entry) = self.item_refs_cache.get(&key) {
            return entry.clone();
        }
        let item_ref =
            self.resolve_item_reference_uncached(state, def_id, generics, assoc_item_resolution);
        self.item_refs_cache.insert(key, item_ref.clone());
        item_ref
    }

    fn resolve_item_reference_uncached(
        &mut self,
        state: &Id::State<'tcx>,
        mut def_id: Id,
        generics: ty::GenericArgsRef<'tcx>,
        assoc_item_resolution: AssocItemResolution,
    ) -> ItemRef<'tcx, Id> {
        use rustc_infer::infer::canonical::ir::TypeVisitableExt;
        let tcx = self.elab_ctx.tcx;
        let typing_env = self.typing_env;
        // Normalize the generics.
        let mut generics = normalize(tcx, typing_env, ty::Unnormalized::new_wip(generics));

        // If this is an associated item, resolve the trait reference.
        let mut trait_info = if assoc_item_resolution != AssocItemResolution::None
            && let Some(tr_def_id) = def_id.parent_of_assoc(state)
            && let Some(self_pred) = tr_def_id.self_pred(state)
        {
            // Substitute to be in the context of the current item.
            let generics = generics.truncate_to(tcx, tr_def_id.generics_of(state));
            let self_pred = ty::EarlyBinder::bind(tcx, self_pred)
                .instantiate(tcx, generics)
                .skip_norm_wip();
            let num_trait_req_clauses =
                ItemPredicates::required_recursively(self.elab_ctx, state, tr_def_id).len();
            Some((self.resolve(state, &self_pred), num_trait_req_clauses))
        } else {
            None
        };

        // If the reference is a known trait impl and the impl implements the target item, we can
        // point directly to the implemented item.
        if assoc_item_resolution == AssocItemResolution::ImplItem
            && let Some((tinfo, _)) = &trait_info
            && let TraitProofKind::Concrete(impl_item_ref) = &tinfo.kind
        {
            // If the item is implemented, point to it; otherwise the item has a default and we're
            // already pointing to it.
            if let Some(implemented_item) = def_id.find_in_impl(state, &impl_item_ref.def_id) {
                def_id = implemented_item;
                generics = generics.rebase_onto(tcx, tinfo.pred.def_id(), impl_item_ref.generics());
            }
            trait_info = None;
        }

        let needs_explicit_self_clause = def_id.takes_explicit_self_clause(state);
        // Rustc gives closures/inline consts extra generics for inference that we don't expose.
        let proper_arg_count = if let Some(parent) = def_id.typeck_parent(state) {
            parent.generics_of(state).count()
        } else {
            generics.len()
        };

        // Determine whether this item reference mentions any of the generic parameters of the owner.
        // We exclude the `dyn` self parameter we add, since that is unrelated to the parent.
        let has_owner_param = generics.has_param() && {
            use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
            use std::ops::ControlFlow;
            struct HasOwnerParam;
            impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for HasOwnerParam {
                type Result = ControlFlow<()>;
                fn visit_ty(&mut self, ty: ty::Ty<'tcx>) -> ControlFlow<()> {
                    match ty.kind() {
                        ty::Param(p) if p.index != DYN_SELF_PARAM_INDEX => ControlFlow::Break(()),
                        _ if ty.has_param() => ty.super_visit_with(self),
                        _ => ControlFlow::Continue(()),
                    }
                }
                fn visit_region(&mut self, r: ty::Region<'tcx>) -> ControlFlow<()> {
                    if r.is_param() {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                }
                fn visit_const(&mut self, c: ty::Const<'tcx>) -> ControlFlow<()> {
                    match c.kind() {
                        ty::ConstKind::Param(_) => ControlFlow::Break(()),
                        _ if c.has_param() => c.super_visit_with(self),
                        _ => ControlFlow::Continue(()),
                    }
                }
            }
            generics.visit_with(&mut HasOwnerParam).is_break()
        };

        let content = ItemRefContents {
            def_id,
            generic_args: generics,
            proper_arg_count,
            in_trait: trait_info,
            needs_explicit_self_clause,
            has_param: generics.has_param()
                || generics.has_escaping_bound_vars()
                || generics.has_free_regions(),
            has_non_lt_param: generics.has_param(),
            has_owner_param,
        };
        content.intern()
    }

    /// Witnesses of the trait clauses required to mention `(def_id, generics)`, e.g. `T: Sized`
    /// for `Option<T>`. If `in_trait`, this is a trait associated item and we only include the
    /// clauses for the item itself.
    pub fn resolve_item_assoc_trait_proofs(
        &mut self,
        state: &Id::State<'tcx>,
        def_id: Id,
        generics: ty::GenericArgsRef<'tcx>,
        in_trait: bool,
    ) -> Vec<TraitProof<'tcx, Id>> {
        let mut trait_proofs =
            self.resolve_item_required_predicates(state, def_id.clone(), generics);
        if in_trait && let Some(tr_def_id) = def_id.parent_of_assoc(state) {
            let num_trait_req_clauses =
                ItemPredicates::required_recursively(self.elab_ctx, state, tr_def_id).len();
            // Assoc consts and methods get an extra `Self: Trait` clause as the first clause, we
            // skip that one too. Note: that clause is the same as `in_trait`.
            let start = num_trait_req_clauses + def_id.takes_explicit_self_clause(state) as usize;
            trait_proofs.drain(..start);
        }
        trait_proofs
    }
}

impl<'tcx, Id: ItemId> ItemRef<'tcx, Id> {
    /// Construct an `ItemRef` for items that can't have generics (e.g. modules).
    pub fn dummy_without_generics(def_id: Id) -> ItemRef<'tcx, Id> {
        let content = ItemRefContents {
            def_id,
            generic_args: Default::default(),
            proper_arg_count: 0,
            in_trait: Default::default(),
            needs_explicit_self_clause: false,
            has_param: false,
            has_non_lt_param: false,
            has_owner_param: false,
        };
        content.intern()
    }

    /// The generics passed to the item.
    pub fn generics(&self) -> GenericArgsRef<'tcx> {
        self.generic_args
    }
    /// The generics passed to the item, except for trait associated items these are only the
    /// generics of the method/type/const itself; generics for the trait are available in
    /// `self.in_trait`.
    pub fn assoc_generics(&self) -> &'tcx [GenericArg<'tcx>] {
        let start = if let Some((tinfo, _)) = &self.in_trait {
            tinfo.pred.skip_binder().args.len()
        } else {
            0
        };
        &self.generic_args[start..self.proper_arg_count]
    }
}

impl<'tcx, Id: ItemId> Deref for ItemRef<'tcx, Id> {
    type Target = ItemRefContents<'tcx, Id>;
    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}
