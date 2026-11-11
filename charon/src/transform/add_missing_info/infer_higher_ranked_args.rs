//! Infer some erased higher-ranked clause arguments.
use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};

#[derive(Visitor)]
struct Infer<'a> {
    traits: &'a IndexMap<TraitDeclId, TraitDecl>,
    binders: BindingStack<GenericParams>,
}

impl VisitorWithBinderStack for Infer<'_> {
    fn binder_stack_mut(&mut self) -> &mut BindingStack<GenericParams> {
        &mut self.binders
    }
}

impl Infer<'_> {
    fn infer(&self, proof: &TraitRef) -> Option<TraitRef> {
        let mut kind = proof.kind.clone();
        // Retrieve the poly trait ref that this proof refers to, along with the provided
        // arguments.
        let (clause, args): (PolyTraitDeclRef, &mut RegionArgs) = match &mut kind {
            TraitRefKind::Clause(var, args) => (
                self.binders
                    .get_var_and_shift(*var, |clause| clause.trait_.clone())?,
                args,
            ),
            TraitRefKind::ParentClause(parent, id, args) => (
                self.traits
                    .get(parent.trait_id())?
                    .implied_clauses
                    .get(*id)?
                    .trait_
                    .clone()
                    .try_substitute_with_tref(parent)
                    .ok()?,
                args,
            ),
            TraitRefKind::ItemClause {
                trait_ref: parent,
                type_id,
                generics,
                clause_id,
                clause_args,
            } => {
                let assoc = self
                    .traits
                    .get(parent.trait_id())?
                    .types
                    .get(*type_id)?
                    .clone()
                    .try_substitute_with_tref(parent)
                    .ok()?;
                let clause = assoc
                    .skip_binder
                    .implied_clauses
                    .get(*clause_id)?
                    .trait_
                    .clone()
                    .try_substitute_with_self(generics, &parent.kind)
                    .ok()?;
                (clause, clause_args)
            }
            _ => return None,
        };
        if !args.regions.iter().any(Region::is_erased) {
            return None;
        }

        // The predicate that this proof proves, this time the cached version.
        let target = RegionBinder::empty(proof.trait_decl_ref.clone());
        // By zipping the two predicates, get a list of args that if applied to `clause` would
        // produce `target`.
        let inferred: RegionArgs = clause.infer_region_mapping(&target)?.no_bound_vars();
        if args.regions.len() != inferred.regions.len() {
            return None;
        }
        // Replace the erased regions in our args with the inferred ones.
        for (arg, inferred) in args.regions.iter_mut().zip(inferred.regions) {
            if arg.is_erased() {
                *arg = inferred;
            }
        }
        // Matching is best-effort. Only retain a reconstruction if it proves exactly the cached
        // predicate.
        if clause.apply(args.clone()) != proof.trait_decl_ref {
            return None;
        }
        Some(TraitRef::new(kind, proof.trait_decl_ref.clone()))
    }
}

impl VisitAstMut for Infer<'_> {
    fn visit<T: AstVisitable>(&mut self, value: &mut T) -> ControlFlow<Self::Break> {
        VisitWithBinderStack::new(self).visit(value)
    }

    fn exit_trait_ref(&mut self, proof: &mut TraitRef) {
        if let Some(recovered) = self.infer(proof) {
            *proof = recovered;
        }
    }
}

pub struct Transform;

impl TransformPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        !options.no_typecheck
    }
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_item_mut(|ctx, mut item| {
            item.drive_mut(&mut Infer {
                traits: &ctx.translated.trait_decls,
                binders: BindingStack::default(),
            });
        });
    }
}
