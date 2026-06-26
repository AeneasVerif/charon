//! We have added an explicit `Self: Trait` clause to the function and global items that correspond
//! to a trait method/associated const declaration. This pass removes the clause in question if it
//! is not used by the item.
use derive_generic_visitor::*;
use std::collections::HashSet;

use crate::ast::*;

use crate::transform::{TransformCtx, ctx::TransformPass};

struct FoundClause;

struct UsesClauseVisitor(TraitClauseId);
impl Visitor for UsesClauseVisitor {
    type Break = FoundClause;
}

/// Visit an item looking for uses of the given clause.
impl VisitAst for UsesClauseVisitor {
    fn visit_trait_clause_id(&mut self, x: &TraitClauseId) -> ControlFlow<Self::Break> {
        if *x == self.0 {
            Break(FoundClause)
        } else {
            Continue(())
        }
    }
    fn visit_trait_param(&mut self, x: &TraitParam) -> ControlFlow<Self::Break> {
        // Don't look at the clause's own id, as this would make every clause count as used.
        // Do look inside the predicate, because another clause may depend on this one.
        self.visit_inner(&x.trait_)
    }
    fn visit_fun_decl(&mut self, x: &FunDecl) -> ControlFlow<Self::Break> {
        if !x.body.has_contents() {
            // For function without bodies we can't know whether the clause is used so we err on
            // the side of it being used.
            return Break(FoundClause);
        }
        self.visit_inner(x)
    }
}

#[derive(Visitor)]
struct RemoveSelfVisitor<'a> {
    remove_in: &'a HashSet<ItemId>,
}

impl RemoveSelfVisitor<'_> {
    fn process_item(&self, id: impl Into<ItemId>, args: &mut GenericArgs) {
        if self.remove_in.contains(&id.into()) {
            args.trait_refs
                .remove_and_shift_ids(TraitClauseId::from_raw(0));
        }
    }
}
impl VisitAstMut for RemoveSelfVisitor<'_> {
    fn enter_type_decl_ref(&mut self, x: &mut TypeDeclRef) {
        match x.id {
            TypeId::Adt(id) => self.process_item(id, &mut x.generics),
            TypeId::Tuple => {}
            TypeId::Builtin(_) => {}
        }
    }
    fn enter_fun_decl_ref(&mut self, x: &mut FunDeclRef) {
        self.process_item(x.id, &mut x.generics);
    }
    fn enter_fn_ptr(&mut self, x: &mut FnPtr) {
        match x.kind.as_ref() {
            FnPtrKind::Fun(FunId::Regular(id)) => self.process_item(*id, &mut x.generics),
            FnPtrKind::Fun(FunId::Builtin(_)) => {}
            FnPtrKind::Trait(..) => {}
        }
    }
    fn enter_global_decl_ref(&mut self, x: &mut GlobalDeclRef) {
        self.process_item(x.id, &mut x.generics);
    }
    fn enter_trait_impl_ref(&mut self, x: &mut TraitImplRef) {
        self.process_item(x.id, &mut x.generics);
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        if !ctx.options.remove_unused_self_clauses {
            return;
        }
        let self_clause_id = TraitClauseId::from_raw(0);
        let mut doesnt_use_self: HashSet<ItemId> = Default::default();

        // We explore only items with an explicit `Self` clause, namely method and associated const
        // declarations.
        for tdecl in &ctx.translated.trait_decls {
            let methods = tdecl
                .methods()
                .filter_map(|m| m.skip_binder.default.as_ref())
                .map(|fn_ref| fn_ref.id);
            // For consts, we need to explore the corresponding initializer body.
            let consts = tdecl
                .consts
                .iter()
                .filter_map(|cst| cst.default.as_ref())
                .filter_map(|gref| ctx.translated.global_decls.get(gref.id))
                .filter_map(|gdecl| gdecl.init_fun_id());
            let funs = methods
                .chain(consts)
                .filter_map(|id: FunDeclId| ctx.translated.fun_decls.get(id));
            for fun in funs {
                match fun.drive(&mut UsesClauseVisitor(self_clause_id)) {
                    Continue(()) => {
                        doesnt_use_self.insert(fun.def_id.into());
                        if let Some(gid) = fun.is_global_initializer {
                            doesnt_use_self.insert(gid.into());
                        }
                    }
                    Break(FoundClause) => {}
                }
            }
        }

        // Remove the now-unused `Self` argument from any `GenericArgs` destined for the items
        // we're about to change. We do this before renumbering the clauses below: a global's
        // `value` is a call to its initializer that forwards the global's own generics (including
        // the `Self` clause as argument 0); removing that argument here keeps the renumbering below
        // from underflowing on the `Self` clause.
        RemoveSelfVisitor {
            remove_in: &doesnt_use_self,
        }
        .visit_by_val_infallible(&mut ctx.translated);

        // In each item, remove the first clause and renumber the others.
        for &id in &doesnt_use_self {
            let Some(mut item) = ctx.translated.get_item_mut(id) else {
                continue;
            };
            item.generic_params()
                .trait_clauses
                .remove_and_shift_ids(self_clause_id);
            item.dyn_visit_mut(|clause_id: &mut TraitClauseId| {
                *clause_id = TraitClauseId::from_usize(clause_id.index() - 1);
            });
        }
    }
}
