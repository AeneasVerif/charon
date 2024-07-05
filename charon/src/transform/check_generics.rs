//! Check that all supplied generic types match the corresponding generic parameters.
use std::fmt::Display;

use derive_visitor::Visitor;

use crate::{ast::*, errors::ErrorCtx, register_error_or_panic};

use super::{ctx::LlbcPass, TransformCtx};

#[derive(Visitor)]
#[visitor(
    TraitImpl(enter),
    GenericArgs(enter),
    AggregateKind(enter),
    FnPtr(enter),
    RawConstantExpr(enter),
    Rvalue(enter),
    TraitClause(enter),
    TraitDeclRef(enter),
    TraitRef(enter),
    Ty(enter)
)]
struct CheckGenericsVisitor<'a, 'ctx> {
    translated: &'a TranslatedCrate,
    error_ctx: &'a mut ErrorCtx<'ctx>,
    // Count how many `GenericArgs` we handled. This is to make sure we don't miss one.
    discharged_args: u32,
    // Tracks an enclosing span to make errors useful.
    item_span: Span,
}

impl CheckGenericsVisitor<'_, '_> {
    fn error(&mut self, message: impl Display) {
        let span = self.item_span;
        let message = message.to_string();
        register_error_or_panic!(self.error_ctx, span, message);
    }

    /// Count that we just discharged one instance of `GenericArgs`.
    fn discharged_one_generics(&mut self) {
        self.discharged_args += 1;
    }

    fn generics_should_be_empty(&mut self, args: &GenericArgs) {
        self.discharged_one_generics();
        if !args.is_empty() {
            self.error("Mismatched generics: should be empty!")
        }
    }
    fn check_generics(&mut self, args: &GenericArgs, params: &GenericParams) {
        self.discharged_one_generics();
        if !args.matches(params) {
            self.error("Mismatched generics!")
        }
    }

    fn generics_should_match_item(&mut self, args: &GenericArgs, item_id: impl Into<AnyTransId>) {
        if let Some(item) = self.translated.get_item(item_id.into()) {
            self.check_generics(args, item.generic_params())
        } else {
            // If the item is missing, we can't check anything but we must still count this.
            self.discharged_one_generics();
        }
    }
    fn check_typeid_generics(&mut self, args: &GenericArgs, ty_kind: &TypeId) {
        match ty_kind {
            TypeId::Adt(id) => self.generics_should_match_item(args, *id),
            TypeId::Tuple => {
                self.discharged_one_generics();
                if !(args.regions.is_empty()
                    && args.const_generics.is_empty()
                    && args.trait_refs.is_empty())
                {
                    self.error("Mismatched generics: generics for a tuple should be only types")
                }
            }
            TypeId::Assumed(..) => {
                // TODO: check generics for built-in types
                self.discharged_one_generics()
            }
        }
    }
}

// Visitor functions
impl CheckGenericsVisitor<'_, '_> {
    fn enter_aggregate_kind(&mut self, agg: &AggregateKind) {
        match agg {
            AggregateKind::Adt(kind, _, args) => {
                self.check_typeid_generics(args, kind);
            }
            AggregateKind::Closure(id, args) => {
                self.generics_should_match_item(args, *id);
            }
            AggregateKind::Array(..) => {}
        }
    }
    fn enter_fn_ptr(&mut self, fn_ptr: &FnPtr) {
        let args = &fn_ptr.generics;
        match &fn_ptr.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(id))
            | FunIdOrTraitMethodRef::Trait(_, _, id) => {
                self.generics_should_match_item(args, *id);
            }
            FunIdOrTraitMethodRef::Fun(FunId::Assumed(..)) => {
                // TODO: check generics for built-in types
                self.discharged_one_generics()
            }
        }
    }
    fn enter_raw_constant_expr(&mut self, cexpr: &RawConstantExpr) {
        if let RawConstantExpr::Global(id, args) = cexpr {
            self.generics_should_match_item(args, *id);
        }
    }
    fn enter_rvalue(&mut self, rvalue: &Rvalue) {
        if let Rvalue::Global(id, args) = rvalue {
            self.generics_should_match_item(args, *id);
        }
    }
    fn enter_trait_clause(&mut self, clause: &TraitClause) {
        self.generics_should_match_item(&clause.generics, clause.trait_id);
    }
    fn enter_trait_decl_ref(&mut self, tref: &TraitDeclRef) {
        self.generics_should_match_item(&tref.generics, tref.trait_id);
    }
    fn enter_trait_ref(&mut self, tref: &TraitRef) {
        let args = &tref.generics;
        match tref.kind {
            TraitRefKind::TraitImpl(id) => self.generics_should_match_item(args, id),
            TraitRefKind::Clause(..)
            | TraitRefKind::ParentClause(..)
            | TraitRefKind::ItemClause(..)
            | TraitRefKind::SelfId
            | TraitRefKind::BuiltinOrAuto(_)
            | TraitRefKind::Dyn(_)
            | TraitRefKind::Unknown(_) => self.generics_should_be_empty(args),
        }
    }
    fn enter_ty(&mut self, ty: &Ty) {
        if let Ty::Adt(kind, args) = ty {
            self.check_typeid_generics(args, kind);
        }
    }

    fn enter_generic_args(&mut self, args: &GenericArgs) {
        if self.discharged_args == 0 {
            // Ensure we counted all `GenericArgs`
            panic!("Unexpected `GenericArgs` in the AST! {args:?}")
        }
        self.discharged_args -= 1;
    }

    // Special case that is not represented as a `GenericArgs`.
    fn enter_trait_impl(&mut self, timpl: &TraitImpl) {
        let Some(tdecl) = self.translated.trait_decls.get(timpl.impl_trait.trait_id) else {
            return;
        };
        let args_match = timpl.parent_trait_refs.len() == tdecl.parent_clauses.len()
            && timpl.types.len() == tdecl.types.len()
            && timpl.consts.len() == tdecl.consts.len();
        if !args_match {
            self.error("The generics supplied by the trait impl don't match the trait decl.")
        }
        let methods = timpl.required_methods.len() == tdecl.required_methods.len();
        if !methods {
            self.error("The methods supplied by the trait impl don't match the trait decl.")
        }
    }
}

pub struct Check;
impl LlbcPass for Check {
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
        for item in ctx.translated.all_items() {
            let mut visitor = CheckGenericsVisitor {
                translated: &ctx.translated,
                error_ctx: &mut ctx.errors,
                discharged_args: 0,
                item_span: item.item_meta().span,
            };
            item.drive(&mut visitor);
            assert_eq!(
                visitor.discharged_args, 0,
                "Got confused about `GenericArgs` locations"
            );
        }
    }
}
