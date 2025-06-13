use derive_generic_visitor::*;
use itertools::Itertools;
use std::collections::HashSet;

use crate::{ast::*, name_matcher::NamePattern};

use super::{ctx::TransformPass, TransformCtx};

#[derive(Visitor)]
struct RemoveMarkersVisitor {
    exclude: HashSet<TraitDeclId>,
}

// Remove clauses and trait refs that mention the offending traits. This relies on the fact that
// `Vector::remove` does not shift indices: it simply leaves an empty slot.
// FIXME: this is a footgun, it caused at least https://github.com/AeneasVerif/charon/issues/561.
impl VisitAstMut for RemoveMarkersVisitor {
    fn enter_generic_params(&mut self, args: &mut GenericParams) {
        let trait_clauses = &mut args.trait_clauses;
        for i in trait_clauses.all_indices() {
            let clause = &trait_clauses[i];
            if self.exclude.contains(&clause.trait_.skip_binder.id) {
                trait_clauses.remove(i);
            }
        }
    }
    fn enter_generic_args(&mut self, args: &mut GenericArgs) {
        let trait_refs = &mut args.trait_refs;
        for i in trait_refs.all_indices() {
            let tref = &trait_refs[i];
            if self.exclude.contains(&tref.trait_decl_ref.skip_binder.id) {
                trait_refs.remove(i);
            }
        }
    }
    fn enter_trait_decl(&mut self, tdecl: &mut TraitDecl) {
        let trait_clauses = &mut tdecl.parent_clauses;
        for i in trait_clauses.all_indices() {
            let clause = &trait_clauses[i];
            if self.exclude.contains(&clause.trait_.skip_binder.id) {
                trait_clauses.remove(i);
            }
        }
    }
    fn enter_trait_impl(&mut self, timpl: &mut TraitImpl) {
        let trait_refs = &mut timpl.parent_trait_refs;
        for i in trait_refs.all_indices() {
            let tref = &trait_refs[i];
            if self.exclude.contains(&tref.trait_decl_ref.skip_binder.id) {
                trait_refs.remove(i);
            }
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Remove any mention of these traits in generic parameters and arguments.
        // We always hide `Allocator` because in `Box` it refers to a type parameter that we always
        // remove.
        let exclude: &[_] = if ctx.options.hide_marker_traits {
            &[
                "core::marker::Sized",
                "core::marker::Tuple",
                "core::marker::Send",
                "core::marker::Sync",
                "core::marker::Unpin",
                "core::alloc::Allocator",
            ]
        } else if ctx.options.raw_boxes {
            &[]
        } else {
            &["core::alloc::Allocator"]
        };

        let exclude: Vec<NamePattern> = exclude
            .into_iter()
            .map(|s| NamePattern::parse(s).unwrap())
            .collect_vec();
        let exclude: HashSet<TraitDeclId> = ctx
            .translated
            .item_names
            .iter()
            .filter(|(_, name)| exclude.iter().any(|p| p.matches(&ctx.translated, name)))
            .filter_map(|(id, _)| id.as_trait_decl())
            .copied()
            .collect();

        for &id in &exclude {
            ctx.translated.trait_decls.remove(id);
        }

        let _ = ctx
            .translated
            .drive_mut(&mut RemoveMarkersVisitor { exclude });
    }
}
