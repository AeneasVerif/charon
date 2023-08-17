//! This file contains various utilities to manipulate generics:
//! - instantiation of binders
//! - checks

#![allow(dead_code)]
use crate::assumed;
use crate::names_utils::item_def_id_to_name;
use hashlink::linked_hash_map::LinkedHashMap;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Clause, FreeRegion, PredicateKind, Region, RegionKind, TyCtxt};

/// Function used for sanity checks: check the constraints given by a definition's
/// generics (lifetime constraints, traits, etc.).
/// For now we simply check that there are no such constraints...
/// TODO: update to use Hax
fn check_generics(tcx: TyCtxt<'_>, def_id: DefId) {
    // Retrieve the generics and the predicates (where-clauses)
    let _generics = tcx.generics_of(def_id);
    // TODO: use predicates_defined_on?
    let preds = tcx.predicates_of(def_id);

    // For now, simply check that there are no where-clauses
    trace!("{:?}", def_id);
    trace!("{:?}", &preds.predicates);
    for (pred, _span) in preds.predicates {
        // Skip the binder (which lists the quantified variables).
        // By doing so, we allow the predicates to contain DeBruijn indices,
        // but it is ok because we only do a simple check.
        let pred_kind = pred.kind().skip_binder();
        match pred_kind {
            PredicateKind::Clause(Clause::Trait(trait_pred)) => {
                // Slightly annoying: some traits are implicit.
                //
                // For instance, whenever we use a type parameter in a definition,
                // Rust implicitly considers it as implementing trait `std::marker::Sized`.
                // For now, we check that there are only instances of this trait,
                // and ignore it.
                use rustc_middle::ty::{BoundConstness, ImplPolarity};
                assert!(trait_pred.polarity == ImplPolarity::Positive);
                // Note sure what this is about
                assert!(trait_pred.constness == BoundConstness::NotConst);
                let trait_name = item_def_id_to_name(tcx, trait_pred.trait_ref.def_id);
                trace!("{}", trait_name);
                assert!(
                    trait_name.equals_ref_name(&assumed::MARKER_SIZED_NAME),
                    "Unsupported trait: {:?}",
                    trait_name
                );
            }
            PredicateKind::Clause(Clause::RegionOutlives(_)) => unimplemented!(),
            PredicateKind::Clause(Clause::TypeOutlives(_)) => unimplemented!(),
            PredicateKind::Clause(Clause::Projection(_)) => unimplemented!(),
            PredicateKind::Clause(Clause::ConstArgHasType(..)) => {
                // I don't really understand that one
            }
            PredicateKind::WellFormed(_) => unimplemented!(),
            PredicateKind::ObjectSafe(_) => unimplemented!(),
            PredicateKind::ClosureKind(_, _, _) => unimplemented!(),
            PredicateKind::Subtype(_) => unimplemented!(),
            PredicateKind::Coerce(_) => unimplemented!(),
            PredicateKind::ConstEvaluatable(_) => unimplemented!(),
            PredicateKind::ConstEquate(_, _) => unimplemented!(),
            PredicateKind::TypeWellFormedFromEnv(_) => unimplemented!(),
            PredicateKind::Ambiguous => unimplemented!(),
            PredicateKind::AliasRelate(..) => unimplemented!(),
        }
    }
}

/// Check a function's generics
pub(crate) fn check_function_generics(tcx: TyCtxt<'_>, def_id: DefId) {
    check_generics(tcx, def_id)
}

/// Check a type's generics
pub(crate) fn check_type_generics(tcx: TyCtxt<'_>, def_id: DefId) {
    check_generics(tcx, def_id)
}

/// Check a global's generics (to refuse them except Sized trait)
pub(crate) fn check_global_generics(tcx: TyCtxt<'_>, def_id: DefId) {
    assert!(tcx.generics_of(def_id).params.is_empty());
    check_generics(tcx, def_id)
}
