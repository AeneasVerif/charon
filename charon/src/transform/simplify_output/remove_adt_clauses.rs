//! `--remove-adt-clauses` strips trait clauses from type declarations when it's possible to do so.
//! Because it's not possible to recover associated type information when we remove clauses,
//! we don't remove clauses if any of them have associated types. For that reason,
//! this flag is best used with `--lift-associated-types`.
//!
//! Every reference to a clause removed in this way is replaced with a `TraitRefKind::BuiltinOrAuto
//! { builtin_data: RemovedAdtClause, .. }`.

use std::collections::HashSet;

use derive_generic_visitor::*;

use crate::ast::*;
use crate::common::CycleDetector;
use crate::ids::{IndexMap, IndexVec};
use crate::transform::{TransformCtx, ctx::TransformPass};

/// Compute whether a trait has associated types, even through supertraits.
fn has_assoc_types(
    translated: &TranslatedCrate,
    cache: &mut IndexMap<TraitDeclId, CycleDetector<bool>>,
    id: TraitDeclId,
) -> bool {
    if cache[id].start_processing() {
        let result = match translated.trait_decls.get(id) {
            Some(tdecl) => {
                !tdecl.types.is_empty()
                    || tdecl
                        .implied_clauses
                        .iter()
                        .any(|p| has_assoc_types(translated, cache, p.trait_.skip_binder.id))
            }
            None => false,
        };
        cache[id].done_processing(result);
    }
    match &cache[id] {
        CycleDetector::Processed(b) => *b,
        CycleDetector::Cyclic | CycleDetector::Processing => false,
        CycleDetector::Unprocessed => unreachable!(),
    }
}

/// ADTs that have at least one trait clause pointing at a trait with associated types
/// (transitively). We leave these ADTs entirely untouched.
fn untouchable_adts(translated: &TranslatedCrate) -> HashSet<TypeDeclId> {
    let mut cache: IndexMap<TraitDeclId, CycleDetector<bool>> = translated
        .trait_decls
        .map_ref_opt(|_| Some(CycleDetector::Unprocessed));
    translated
        .type_decls
        .iter()
        .filter(|d| {
            d.generics
                .trait_clauses
                .iter()
                .any(|c| has_assoc_types(translated, &mut cache, c.trait_.skip_binder.id))
        })
        .map(|d| d.def_id)
        .collect()
}

#[derive(Visitor)]
struct RemoveAdtClausesVisitor<'a> {
    translated: &'a TranslatedCrate,
    untouchable_adts: &'a HashSet<TypeDeclId>,
    binder_stack: BindingStack<GenericParams>,
}

impl VisitorWithBinderStack for RemoveAdtClausesVisitor<'_> {
    fn binder_stack_mut(&mut self) -> &mut BindingStack<GenericParams> {
        &mut self.binder_stack
    }
}

impl VisitAstMut for RemoveAdtClausesVisitor<'_> {
    fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ::std::ops::ControlFlow<Self::Break> {
        VisitWithBinderStack::new(self).visit(x)?;
        ::std::ops::ControlFlow::Continue(())
    }

    fn enter_type_decl(&mut self, decl: &mut TypeDecl) {
        if self.untouchable_adts.contains(&decl.def_id) {
            return;
        }
        decl.generics.trait_clauses.clear();
        decl.generics.trait_type_constraints.clear();
        // The wrapper has already pushed the (uncleared) generic params onto the binder stack.
        // Replace the top with the cleared version so dangling-clause detection works as we
        // descend into the body.
        *self.binder_stack.innermost_mut() = decl.generics.clone();
    }

    fn enter_type_decl_ref(&mut self, tref: &mut TypeDeclRef) {
        if let TypeId::Adt(id) = tref.id
            && !self.untouchable_adts.contains(&id)
        {
            tref.generics.trait_refs.clear();
        }
    }

    fn enter_trait_ref(&mut self, tref: &mut TraitRef) {
        let TraitRefKind::Clause(var) = &tref.kind else {
            return;
        };
        if self
            .binder_stack
            .get_var::<_, GenericParams>(*var)
            .is_some()
        {
            return;
        }
        let new_kind = build_removed_clause_placeholder(self.translated, &tref.trait_decl_ref);
        tref.with_contents_mut(|contents| contents.kind = new_kind);
    }
}

/// Build a `BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }` kind whose `parent_trait_refs`
/// recursively mirror the trait's implied clauses (each parent itself a `RemovedAdtClause`
/// placeholder).
///
/// Substitution into the parents' `trait_decl_ref`s uses a stub placeholder kind for `Self`
/// rather than the original (dangling) `Clause(var)`: otherwise we'd embed dangling clause refs
/// inside the synthesized parents, and the visitor never re-enters them.
fn build_removed_clause_placeholder(
    translated: &TranslatedCrate,
    trait_decl_ref: &PolyTraitDeclRef,
) -> TraitRefKind {
    let trait_id = trait_decl_ref.skip_binder.id;
    let stub_tref = TraitRef::new(
        TraitRefKind::BuiltinOrAuto {
            builtin_data: BuiltinImplData::RemovedAdtClause,
            parent_trait_refs: Default::default(),
            types: Default::default(),
        },
        trait_decl_ref.clone(),
    );
    let parent_trait_refs: IndexVec<TraitClauseId, TraitRef> = translated
        .trait_decls
        .get(trait_id)
        .map(|tdecl| {
            Substituted::new_for_trait_ref(&tdecl.implied_clauses, &stub_tref)
                .iter()
                .map(|s| {
                    let parent: TraitParam = s.substitute();
                    let kind = build_removed_clause_placeholder(translated, &parent.trait_);
                    TraitRef::new(kind, parent.trait_)
                })
                .collect()
        })
        .unwrap_or_default();
    TraitRefKind::BuiltinOrAuto {
        builtin_data: BuiltinImplData::RemovedAdtClause,
        parent_trait_refs,
        types: Default::default(),
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        if !ctx.options.remove_adt_clauses {
            return;
        }
        let untouchable = untouchable_adts(&ctx.translated);
        ctx.for_each_item_mut(|ctx, mut item| {
            let _ = item.drive_mut(&mut RemoveAdtClausesVisitor {
                translated: &ctx.translated,
                untouchable_adts: &untouchable,
                binder_stack: BindingStack::empty(),
            });
        });
    }
}
