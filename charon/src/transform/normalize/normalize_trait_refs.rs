use crate::{
    ast::*,
    ids::{IndexMap, IndexVec},
    transform::{TransformCtx, ctx::TransformPass},
};

const MAX_NORMALIZATION_STEPS: usize = 100;

#[derive(Visitor)]
struct NormalizeTraitRefs<'a> {
    impl_parent_refs: &'a IndexMap<TraitImplId, IndexVec<TraitClauseId, TraitRef>>,
    /// Charon can end up with self-referential clauses, see e.g.
    /// `issue-1078-default-assoc-ty-self-ref-clause.rs`. Therefore we simply give up normalizing
    /// after a number of steps.
    steps: usize,
}

impl VisitAstMut for NormalizeTraitRefs<'_> {
    fn exit_trait_ref(&mut self, tref: &mut TraitRef) {
        if self.steps >= MAX_NORMALIZATION_STEPS {
            return;
        }
        if let TraitRefKind::ParentClause(parent, clause_id) = &tref.kind {
            *tref = match &parent.kind {
                TraitRefKind::TraitImpl(impl_ref) => {
                    let Some(proof) = self.impl_parent_refs.get(impl_ref.id) else {
                        return;
                    };
                    let mut proof = ItemBinder::new(impl_ref.id, proof[*clause_id].clone())
                        .substitute(ItemBinder::new(CurrentItem, &impl_ref.generics))
                        .under_current_binder();
                    if *tref == proof {
                        return;
                    }
                    // Recursively normalize.
                    self.steps += 1;
                    self.visit(&mut proof);
                    proof
                }
                TraitRefKind::BuiltinOrAuto {
                    parent_trait_refs, ..
                } => {
                    let Some(proof) = parent_trait_refs.get(*clause_id) else {
                        return;
                    };
                    proof.clone()
                }
                _ => return,
            };
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        !options.no_normalize
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Items are temporarily removed from the crate while we mutate them, so keep the original
        // impl proofs separately.
        let impl_parent_refs = ctx
            .translated
            .trait_impls
            .map_ref(|timpl| timpl.implied_trait_refs.clone());
        ctx.for_each_item_mut(|_, mut item| {
            let _ = item.drive_mut(&mut NormalizeTraitRefs {
                impl_parent_refs: &impl_parent_refs,
                steps: 0,
            });
        });
    }
}
