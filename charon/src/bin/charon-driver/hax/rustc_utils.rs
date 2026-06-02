use std::collections::HashSet;

use rustc_hir::def::DefKind as RDefKind;
use rustc_middle::{mir, ty};
use rustc_span::kw;
use rustc_type_ir::Interner;

use crate::hax::prelude::*;

pub fn inst_binder<'tcx, T>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    args: Option<ty::GenericArgsRef<'tcx>>,
    x: ty::EarlyBinder<'tcx, T>,
) -> T
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>> + Clone,
{
    match args {
        None => x.instantiate_identity().skip_normalization(),
        Some(args) => normalize(tcx, typing_env, x.instantiate(tcx, args)),
    }
}

pub fn substitute<'tcx, T>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    args: Option<ty::GenericArgsRef<'tcx>>,
    x: T,
) -> T
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
{
    inst_binder(tcx, typing_env, args, ty::EarlyBinder::bind(x))
}

/// Make a new `ParamEnv` from a list of clauses.
pub fn param_env_from_clauses<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    predicates: impl Iterator<Item = ty::Clause<'tcx>>,
) -> ty::ParamEnv<'tcx> {
    let cause = rustc_trait_selection::traits::ObligationCause::dummy();
    let param_env = ty::ParamEnv::new(tcx.mk_clauses_from_iter(predicates));
    rustc_trait_selection::traits::normalize_param_env_or_error(tcx, param_env, cause)
}

#[extension_traits::extension(pub trait SubstBinder)]
impl<'tcx, T: ty::TypeFoldable<ty::TyCtxt<'tcx>>> ty::Binder<'tcx, T> {
    fn subst(
        self,
        tcx: ty::TyCtxt<'tcx>,
        generics: &[ty::GenericArg<'tcx>],
    ) -> ty::Binder<'tcx, T> {
        ty::EarlyBinder::bind(self)
            .instantiate(tcx, generics)
            .skip_normalization()
    }
}

/// Whether the item can have generic parameters.
pub(crate) fn can_have_generics<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> bool {
    use RDefKind::*;
    !matches!(
        get_def_kind(tcx, def_id),
        ConstParam
            | ExternCrate
            | ForeignMod
            | GlobalAsm
            | LifetimeParam
            | Macro(..)
            | Mod
            | TyParam
            | Use
    )
}

pub(crate) fn get_variant_kind<'s, S: UnderOwnerState<'s>>(
    adt_def: &ty::AdtDef<'s>,
    variant_index: rustc_abi::VariantIdx,
    _s: &S,
) -> VariantKind {
    if adt_def.is_struct() {
        VariantKind::Struct
    } else if adt_def.is_union() {
        VariantKind::Union
    } else {
        let index = variant_index;
        VariantKind::Enum { index }
    }
}

/// Gets the children of a module.
pub fn get_mod_children<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: RDefId,
) -> Vec<(Option<rustc_span::Ident>, RDefId)> {
    match def_id.as_local() {
        Some(ldid) => match tcx.hir_node_by_def_id(ldid) {
            rustc_hir::Node::Crate(m)
            | rustc_hir::Node::Item(&rustc_hir::Item {
                kind: rustc_hir::ItemKind::Mod(_, m),
                ..
            }) => m
                .item_ids
                .iter()
                .map(|&item_id| {
                    let opt_ident = tcx.hir_item(item_id).kind.ident();
                    let def_id = item_id.owner_id.to_def_id();
                    (opt_ident, def_id)
                })
                .collect(),
            node => panic!("DefKind::Module is an unexpected node: {node:?}"),
        },
        None => tcx
            .module_children(def_id)
            .iter()
            .filter_map(|child| Some((Some(child.ident), child.res.opt_def_id()?)))
            .collect(),
    }
}

/// Gets the children of an `extern` block. Empty if the block is not defined in the current crate.
pub fn get_foreign_mod_children<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> Vec<RDefId> {
    match def_id.as_local() {
        Some(ldid) => tcx
            .hir_node_by_def_id(ldid)
            .expect_item()
            .expect_foreign_mod()
            .1
            .iter()
            .map(|foreign_item_ref| foreign_item_ref.owner_id.to_def_id())
            .collect(),
        None => vec![],
    }
}

/// The signature of a method impl may be a subtype of the one expected from the trait decl, as in
/// the example below. For correctness, we must be able to map from the method generics declared in
/// the trait to the actual method generics. Because this would require type inference, we instead
/// simply return the declared signature. This will cause issues if it is possible to use such a
/// more-specific implementation with its more-specific type, but we have a few other issues with
/// lifetime-generic function pointers anyway so this is unlikely to cause problems.
///
/// ```ignore
/// trait MyCompare<Other>: Sized {
///     fn compare(self, other: Other) -> bool;
/// }
/// impl<'a> MyCompare<&'a ()> for &'a () {
///     // This implementation is more general because it works for non-`'a` refs. Note that only
///     // late-bound vars may differ in this way.
///     // `<&'a () as MyCompare<&'a ()>>::compare` has type `fn<'b>(&'a (), &'b ()) -> bool`,
///     // but type `fn(&'a (), &'a ()) -> bool` was expected from the trait declaration.
///     fn compare<'b>(self, _other: &'b ()) -> bool {
///         true
///     }
/// }
/// ```
pub fn get_method_sig<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: RDefId,
    method_args: Option<ty::GenericArgsRef<'tcx>>,
) -> ty::PolyFnSig<'tcx> {
    let real_sig = inst_binder(tcx, typing_env, method_args, tcx.fn_sig(def_id));
    let item = tcx.associated_item(def_id);
    let ty::AssocContainer::TraitImpl(Ok(decl_method_id)) = item.container else {
        return real_sig;
    };
    let declared_sig = tcx.fn_sig(decl_method_id);

    let impl_def_id = item.container_id(tcx);
    let method_args =
        method_args.unwrap_or_else(|| ty::GenericArgs::identity_for_item(tcx, def_id));
    // The trait predicate that is implemented by the surrounding impl block.
    let implemented_trait_ref = tcx
        .impl_trait_ref(impl_def_id)
        .instantiate(tcx, method_args);
    let implemented_trait_ref = normalize(tcx, typing_env, implemented_trait_ref);
    // Construct arguments for the declared method generics in the context of the implemented
    // method generics.
    let decl_args = method_args.rebase_onto(tcx, impl_def_id, implemented_trait_ref.args);
    let sig = declared_sig.instantiate(tcx, decl_args);
    let sig = normalize(tcx, typing_env, sig);

    if let container_named_lts = tcx
        .generics_of(impl_def_id)
        .own_params
        .iter()
        .filter(|p| matches!(p.kind, ty::GenericParamDefKind::Lifetime))
        .filter(|p| p.name != kw::UnderscoreLifetime)
        .map(|p| p.name)
        .collect::<HashSet<_>>()
        && sig
            .bound_vars()
            .iter()
            .map(|v| v.expect_region())
            .filter_map(|v| v.get_name(tcx))
            .any(|lt| container_named_lts.contains(&lt))
    {
        // Avoids using the same lifetime name twice in the same scope (once in impl parameters,
        // second in the method declaration late-bound vars).
        tcx.anonymize_bound_vars(sig)
    } else {
        sig
    }
}

/// Generates a list of `<trait_ref>::Ty` type aliases for each non-gat associated type of the
/// given trait and its parents, in a specific order.
pub fn assoc_tys_for_trait<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    tref: ty::TraitRef<'tcx>,
) -> Vec<ty::AliasTy<'tcx>> {
    fn gather_assoc_tys<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        assoc_tys: &mut Vec<ty::AliasTy<'tcx>>,
        tref: ty::TraitRef<'tcx>,
    ) {
        assoc_tys.extend(
            tcx.associated_items(tref.def_id)
                .in_definition_order()
                .filter(|assoc| matches!(assoc.kind, ty::AssocKind::Type { .. }))
                .filter(|assoc| {
                    tcx.generics_of(assoc.def_id).own_params.is_empty()
                        && tcx.predicates_of(assoc.def_id).predicates.is_empty()
                })
                .map(|assoc| {
                    ty::AliasTy::new(tcx, tcx.alias_ty_kind_from_def_id(assoc.def_id), tref.args)
                }),
        );
        for clause in tcx
            .explicit_super_predicates_of(tref.def_id)
            .map_bound(|clauses| clauses.iter().map(|(clause, _span)| *clause))
            .iter_instantiated(tcx, tref.args)
        {
            if let Some(pred) = clause.as_trait_clause() {
                let tref = erase_and_norm(tcx, typing_env, pred.map(|b| b.skip_binder().trait_ref));
                gather_assoc_tys(tcx, typing_env, assoc_tys, tref);
            }
        }
    }
    let mut ret = vec![];
    gather_assoc_tys(tcx, typing_env, &mut ret, tref);
    ret
}

/// Generates a `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` type for the given trait ref.
pub fn dyn_self_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    tref: ty::TraitRef<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    let re_erased = tcx.lifetimes.re_erased;
    if !tcx.is_dyn_compatible(tref.def_id) {
        return None;
    }

    // The main `Trait<Args>` predicate.
    let main_pred = ty::Binder::dummy(ty::ExistentialPredicate::Trait(
        ty::ExistentialTraitRef::erase_self_ty(tcx, tref),
    ));

    let ty_constraints = assoc_tys_for_trait(tcx, typing_env, tref)
        .into_iter()
        .map(|alias_ty| {
            let proj = ty::ProjectionPredicate {
                projection_term: alias_ty.into(),
                term: ty::Ty::new_alias(tcx, alias_ty).into(),
            };
            let proj = ty::ExistentialProjection::erase_self_ty(tcx, proj);
            ty::Binder::dummy(ty::ExistentialPredicate::Projection(proj))
        });

    let preds = {
        // Stable sort predicates to prevent platform-specific ordering issues
        let mut preds: Vec<_> = [main_pred].into_iter().chain(ty_constraints).collect();
        preds.sort_by(|a, b| {
            use rustc_middle::ty::ExistentialPredicateStableCmpExt;
            a.skip_binder().stable_cmp(tcx, &b.skip_binder())
        });
        tcx.mk_poly_existential_predicates(&preds)
    };
    let ty = tcx.mk_ty_from_kind(ty::Dynamic(preds, re_erased));
    let ty = normalize(tcx, typing_env, ty::Unnormalized::new_wip(ty));
    Some(ty)
}

pub fn closure_once_shim<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    closure_ty: ty::Ty<'tcx>,
) -> Option<mir::Body<'tcx>> {
    let ty::Closure(def_id, args) = closure_ty.kind() else {
        unreachable!()
    };
    let instance = match args.as_closure().kind() {
        ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
            ty::Instance::fn_once_adapter_instance(tcx, *def_id, args)
        }
        ty::ClosureKind::FnOnce => return None,
    };
    let mir = tcx.instance_mir(instance.def).clone();
    let mir = ty::EarlyBinder::bind(mir)
        .instantiate(tcx, instance.args)
        .skip_normalization();
    Some(mir)
}

pub fn drop_glue_shim<'tcx>(
    s: &impl UnderOwnerState<'tcx>,
    def_id: &DefId,
    instantiate: Option<ty::GenericArgsRef<'tcx>>,
) -> mir::Body<'tcx> {
    let tcx = s.base().tcx;
    let drop_in_place = tcx.require_lang_item(rustc_hir::LangItem::DropGlue, rustc_span::DUMMY_SP);
    let ty = inst_binder(tcx, s.typing_env(), instantiate, def_id.type_of(s));
    let mut body =
        rustc_mir_transform::build_drop_shim(tcx, drop_in_place, Some(ty), s.typing_env());
    // Set the mir phase so that charon knows the contained drops are precise.
    body.phase = mir::MirPhase::Runtime(mir::RuntimePhase::Optimized);
    body
}
