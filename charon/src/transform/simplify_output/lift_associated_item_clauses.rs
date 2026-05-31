//! Move clauses on non-generic associated types to be implied clauses of the trait. The
//! distinction is not semantically meaningful.
use std::mem;

use crate::{
    ast::*,
    ids::{IndexMap, IndexVec},
};

use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;
impl TransformPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        !options.no_normalize
    }
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // For each trait, we move the item-local clauses to be top-level parent clauses, and
        // record the mapping from the old to the new ids.
        let trait_item_clause_ids: IndexMap<
            TraitDeclId,
            IndexMap<AssocTypeId, IndexVec<TraitClauseId, TraitClauseId>>,
        > = ctx.translated.trait_decls.map_ref_mut(|decl| {
            let mut map = IndexMap::default();
            for (type_id, assoc_ty) in decl
                .types
                .iter_mut_enumerated()
                .filter(|(_, assoc_ty)| !assoc_ty.params.has_explicits())
            {
                // Try to move them all out of the binder, or bail.
                if let Some(clauses) = assoc_ty
                    .skip_binder
                    .clone()
                    .implied_clauses
                    .move_from_under_binder()
                {
                    assoc_ty.skip_binder.implied_clauses.clear();
                    let id_map = clauses.map(|mut clause| {
                        decl.implied_clauses.push_with(|id| {
                            clause.clause_id = id;
                            clause
                        })
                    });
                    if assoc_ty.params.trait_clauses.is_empty() {
                        // Move non-trait-clause-predicates of non-GAT types to be predicates on
                        // the trait itself.
                        decl.generics.take_predicates_from(
                            mem::take(&mut assoc_ty.params)
                                .move_from_under_binder()
                                .unwrap(),
                        );
                    }
                    map.set_slot_extend(type_id, id_map);
                }
            }
            map
        });

        // Move the item-local trait refs to match what we did in the trait declarations.
        for timpl in ctx.translated.trait_impls.iter_mut() {
            for (type_id, assoc_ty) in timpl.types.iter_mut_indexed() {
                if let Some(m) = trait_item_clause_ids.get(timpl.impl_trait.id)
                    && m.get(type_id).is_some()
                {
                    for trait_ref in mem::take(&mut assoc_ty.skip_binder.implied_trait_refs) {
                        let trait_ref = trait_ref.move_from_under_binder().unwrap();
                        // Note: this assumes that we listed the types in the same order as in the
                        // trait decl, which we do.
                        timpl.implied_trait_refs.push(trait_ref);
                    }
                }
            }
        }

        // Update trait refs.
        ctx.translated.dyn_visit_mut(|trkind: &mut TraitRefKind| {
            use TraitRefKind::*;
            match trkind {
                ItemClause(..) => take_mut::take(trkind, |trkind| {
                    let ItemClause(tref, type_id, item_clause_id) = trkind else {
                        unreachable!()
                    };
                    let new_id = (|| {
                        let new_id = *trait_item_clause_ids
                            .get(tref.trait_decl_ref.skip_binder.id)?
                            .get(type_id)?
                            .get(item_clause_id)?;
                        Some(new_id)
                    })();
                    match new_id {
                        Some(new_id) => ParentClause(tref, new_id),
                        None => ItemClause(tref, type_id, item_clause_id),
                    }
                }),
                BuiltinOrAuto {
                    parent_trait_refs,
                    types,
                    ..
                } => {
                    for assoc_ty in types.iter_mut() {
                        for tref in std::mem::take(&mut assoc_ty.implied_trait_refs) {
                            // Note: this assumes that we listed the types in the same order as in
                            // the trait decl, which we do.
                            parent_trait_refs.push(tref);
                        }
                    }
                }
                _ => {}
            }
        });
    }
}
