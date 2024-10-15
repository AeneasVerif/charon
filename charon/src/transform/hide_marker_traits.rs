use std::collections::HashSet;

use derive_visitor::{DriveMut, VisitorMut};
use index_vec::Idx;
use itertools::Itertools;

use crate::{ast::*, name_matcher::NamePattern};

use super::{ctx::TransformPass, TransformCtx};

#[derive(VisitorMut)]
#[visitor(
    GenericParams(enter),
    GenericArgs(enter),
    TraitDecl(enter),
    TraitImpl(enter)
)]
struct Visitor {
    exclude: HashSet<TraitDeclId>,
}

// Remove clauses and trait refs that mention the offending traits. This relies on the fact that
// `Vector::remove` does not shift indices: it simply leaves an empty slot.
impl Visitor {
    fn enter_generic_params(&mut self, args: &mut GenericParams) {
        let trait_clauses = &mut args.trait_clauses;
        for i in 0..trait_clauses.len() {
            let clause = &trait_clauses[i];
            if self.exclude.contains(&clause.trait_.skip_binder.trait_id) {
                trait_clauses.remove(<_ as Idx>::from_usize(i));
            }
        }
    }
    fn enter_generic_args(&mut self, args: &mut GenericArgs) {
        let trait_refs = &mut args.trait_refs;
        for i in 0..trait_refs.len() {
            let tref = &trait_refs[i];
            if self
                .exclude
                .contains(&tref.trait_decl_ref.skip_binder.trait_id)
            {
                trait_refs.remove(<_ as Idx>::from_usize(i));
            }
        }
    }
    fn enter_trait_decl(&mut self, tdecl: &mut TraitDecl) {
        let trait_clauses = &mut tdecl.parent_clauses;
        for i in 0..trait_clauses.len() {
            let clause = &trait_clauses[i];
            if self.exclude.contains(&clause.trait_.skip_binder.trait_id) {
                trait_clauses.remove(<_ as Idx>::from_usize(i));
            }
        }
    }
    fn enter_trait_impl(&mut self, timpl: &mut TraitImpl) {
        let trait_refs = &mut timpl.parent_trait_refs;
        for i in 0..trait_refs.len() {
            let tref = &trait_refs[i];
            if self
                .exclude
                .contains(&tref.trait_decl_ref.skip_binder.trait_id)
            {
                trait_refs.remove(<_ as Idx>::from_usize(i));
            }
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
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

        ctx.translated.drive_mut(&mut Visitor { exclude });
    }
}
