use std::{ops::Deref, sync::Arc};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, GenericArg, GenericArgsRef};

use crate::{ImplExpr, ImplExprAtom, ItemPredicates, PredicateSearcher, normalize, self_predicate};

/// Reference to an item, with generics as well as `ImplExpr`s for the required predicates.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ItemRef<'tcx> {
    // TODO: intern?
    contents: Arc<ItemRefContents<'tcx>>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ItemRefContents<'tcx> {
    /// The item being refered to.
    pub def_id: DefId,
    /// The arguments provided to this item.
    pub generic_args: ty::GenericArgsRef<'tcx>,
    /// Witnesses of the trait clauses required by the item, e.g. `T: Sized` for `Option<T>`.
    pub impl_exprs: Vec<ImplExpr<'tcx>>,
    /// If we're referring to a trait associated item, this gives the trait clause/impl we're
    /// referring to, as well as the number of clauses required to mention the trait (cached for
    /// easy access).
    pub in_trait: Option<(ImplExpr<'tcx>, usize)>,
    /// Whether this item is an associated type.
    pub is_assoc_ty: bool,
    /// Whether this contains any reference to a type/lifetime/const parameter.
    pub has_param: bool,
    /// Whether this contains any reference to a type/const parameter.
    pub has_non_lt_param: bool,
}

impl<'tcx> ItemRefContents<'tcx> {
    fn intern(self) -> ItemRef<'tcx> {
        ItemRef {
            contents: Arc::new(self),
        }
    }
}

impl<'tcx> PredicateSearcher<'tcx> {
    /// Construct an `ItemRef` by filling in the trait proofs required to mention said item.
    ///
    /// If `resolve_assoc_item_trait_ref == true` and `(def_id, generics)` points to a trait
    /// associated item that can be resolved to a specific `impl`, `translate` rewrites `def_id` to
    /// the concrete associated item from that `impl` and rebases the generics.
    ///
    /// For instance, [`<u32 as From<u8>>::from`] produces a [`ItemRef`] with a [`DefId`] looking
    /// like `core::convert::num::Impl#42::from` when `resolve_impl` is `true`, otherwise keeps the
    /// `DefId` of the trait item definition: `core::convert::From::from`.
    pub fn resolve_item_reference(
        &mut self,
        mut def_id: DefId,
        generics: ty::GenericArgsRef<'tcx>,
        // If this is an associated item, resolve the trait reference it is based on.
        resolve_assoc_item_trait_ref: bool,
    ) -> ItemRef<'tcx> {
        // TODO: cache elaboration
        use rustc_infer::infer::canonical::ir::TypeVisitableExt;
        let tcx = self.tcx;
        let typing_env = self.typing_env;
        // Normalize the generics.
        let mut generics = normalize(tcx, typing_env, generics);

        if tcx.is_typeck_child(def_id) {
            // Rustc gives closures/inline consts extra generic for inference that we don't care about.
            generics = generics.truncate_to(tcx, tcx.generics_of(tcx.typeck_root_def_id(def_id)));
        }

        // If this is an associated item, resolve the trait reference.
        let mut trait_info =
            if resolve_assoc_item_trait_ref && let Some(tr_def_id) = tcx.trait_of_assoc(def_id) {
                // The "self" predicate in the context of the trait.
                let self_pred = self_predicate(tcx, tr_def_id);
                // Substitute to be in the context of the current item.
                let generics = generics.truncate_to(tcx, tcx.generics_of(tr_def_id));
                let self_pred = ty::EarlyBinder::bind(self_pred).instantiate(tcx, generics);
                let num_trait_req_clauses =
                    ItemPredicates::required_recursively(tcx, tr_def_id, &self.options).len();
                // TODO: cache resolution
                Some((self.resolve(&self_pred), num_trait_req_clauses))
            } else {
                None
            };

        // If the reference is a known trait impl and the impl implements the target item, we can
        // point directly to the implemented item.
        if let Some((tinfo, _)) = &trait_info
            && let ImplExprAtom::Concrete(impl_item_ref) = &tinfo.r#impl
            && let Some(implemented_item) = tcx
                .associated_items(impl_item_ref.def_id)
                .in_definition_order()
                .find(|item| item.trait_item_def_id() == Some(def_id))
        {
            let trait_def_id = tcx.parent(def_id);
            def_id = implemented_item.def_id;
            generics = generics.rebase_onto(tcx, trait_def_id, impl_item_ref.generics());
            trait_info = None;
        }

        let impl_exprs = self.resolve_item_required_predicates(def_id, generics);

        let content = ItemRefContents {
            def_id,
            generic_args: generics,
            impl_exprs,
            in_trait: trait_info,
            is_assoc_ty: matches!(tcx.def_kind(def_id), DefKind::AssocTy),
            has_param: generics.has_param()
                || generics.has_escaping_bound_vars()
                || generics.has_free_regions(),
            has_non_lt_param: generics.has_param(),
        };
        content.intern()
    }
}

impl<'tcx> ItemRef<'tcx> {
    /// Construct an `ItemRef` for items that can't have generics (e.g. modules).
    pub fn dummy_without_generics(def_id: DefId) -> ItemRef<'tcx> {
        let content = ItemRefContents {
            def_id,
            generic_args: Default::default(),
            impl_exprs: Default::default(),
            in_trait: Default::default(),
            is_assoc_ty: false,
            has_param: false,
            has_non_lt_param: false,
        };
        content.intern()
    }

    /// The generics passed to the item.
    pub fn generics(&self) -> GenericArgsRef<'tcx> {
        self.generic_args
    }
    /// The trait proofs passed to the item.
    pub fn impl_exprs(&self) -> &[ImplExpr<'tcx>] {
        &self.impl_exprs
    }
    /// The generics passed to the item, except for trait associated items these are only the
    /// generics of the method/type/const itself; generics for the trait are available in
    /// `self.in_trait`.
    pub fn assoc_generics(&self) -> &'tcx [GenericArg<'tcx>] {
        let start = if let Some((tinfo, _)) = &self.in_trait {
            tinfo.r#trait.skip_binder().args.len()
        } else {
            0
        };
        &self.generic_args[start..]
    }
    /// The trait proofs passed to the item, except for trait associated items these are only the
    /// proofs of the method/type/const itself.
    pub fn assoc_impl_exprs(&self) -> &[ImplExpr<'tcx>] {
        let start = if let Some((_, num_trait_req_clauses)) = self.in_trait {
            // Assoc consts and methods get an extra `Self: Trait` clause as the first clause, we
            // skip that one too. Note: that clause is the same as `self.in_trait`.
            num_trait_req_clauses + if self.is_assoc_ty { 0 } else { 1 }
        } else {
            0
        };
        &self.impl_exprs[start..]
    }
}

impl<'tcx> Deref for ItemRef<'tcx> {
    type Target = ItemRefContents<'tcx>;
    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}
