//! Check that all supplied generic types match the corresponding generic parameters.
use derive_generic_visitor::*;
use std::fmt::Display;

use crate::{errors::ErrorCtx, llbc_ast::*, register_error_or_panic};

use super::{ctx::TransformPass, TransformCtx};

#[derive(Visitor)]
struct CheckGenericsVisitor<'a> {
    translated: &'a TranslatedCrate,
    error_ctx: &'a mut ErrorCtx,
    // Count how many `GenericArgs` we handled. This is to make sure we don't miss one.
    discharged_args: u32,
    // Tracks an enclosing span to make errors useful.
    item_span: Span,
}

impl CheckGenericsVisitor<'_> {
    fn error(&mut self, message: impl Display) {
        let span = self.item_span;
        let message = message.to_string();
        register_error_or_panic!(self.error_ctx, self.translated, span, message);
    }

    /// Count that we just discharged one instance of `GenericArgs`.
    fn discharged_one_generics(&mut self) {
        self.discharged_args += 1;
    }

    fn generics_should_match_item(&mut self, args: &GenericArgs, item_id: impl Into<AnyTransId>) {
        self.discharged_one_generics();
        if let Some(item) = self.translated.get_item(item_id.into()) {
            let params = item.generic_params();
            if !args.matches(params) {
                self.error(format!(
                    "Mismatched generics:\nexpected: {params:?}\n     got: {args:?}"
                ))
            }
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
            TypeId::Builtin(..) => {
                // TODO: check generics for built-in types
                self.discharged_one_generics()
            }
        }
    }
}

// Visitor functions
impl VisitAst for CheckGenericsVisitor<'_> {
    fn enter_aggregate_kind(&mut self, agg: &AggregateKind) {
        match agg {
            AggregateKind::Adt(kind, _, _, args) => {
                self.check_typeid_generics(args, kind);
            }
            AggregateKind::Closure(_id, _args) => {
                // TODO(#194): handle closure generics properly
                // self.generics_should_match_item(args, *id);
                self.discharged_one_generics()
            }
            AggregateKind::Array(..) => {}
        }
    }
    fn enter_fn_ptr(&mut self, fn_ptr: &FnPtr) {
        match &fn_ptr.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(id)) => {
                let args = &fn_ptr.generics;
                self.generics_should_match_item(args, *id);
            }
            FunIdOrTraitMethodRef::Trait(tref, _, id) => {
                let args = tref
                    .trait_decl_ref
                    .skip_binder
                    .generics
                    .clone()
                    .concat(&fn_ptr.generics);
                self.generics_should_match_item(&args, *id);
            }
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(..)) => {
                // TODO: check generics for built-in types
                self.discharged_one_generics()
            }
        }
    }
    fn enter_fun_decl_ref(&mut self, fun_ref: &FunDeclRef) {
        self.generics_should_match_item(&fun_ref.generics, fun_ref.id);
    }
    fn enter_global_decl_ref(&mut self, global_ref: &GlobalDeclRef) {
        self.generics_should_match_item(&global_ref.generics, global_ref.id);
    }
    fn enter_trait_decl_ref(&mut self, tref: &TraitDeclRef) {
        self.generics_should_match_item(&tref.generics, tref.trait_id);
    }
    fn enter_trait_impl_ref(&mut self, impl_ref: &TraitImplRef) {
        self.generics_should_match_item(&impl_ref.generics, impl_ref.impl_id);
    }
    fn enter_trait_ref(&mut self, tref: &TraitRef) {
        match &tref.kind {
            TraitRefKind::TraitImpl(id, args) => self.generics_should_match_item(args, *id),
            TraitRefKind::BuiltinOrAuto(..)
            | TraitRefKind::Dyn(..)
            | TraitRefKind::Clause(..)
            | TraitRefKind::ParentClause(..)
            | TraitRefKind::ItemClause(..)
            | TraitRefKind::SelfId
            | TraitRefKind::Unknown(_) => {}
        }
    }
    fn enter_ty(&mut self, ty: &Ty) {
        if let TyKind::Adt(kind, args) = ty.kind() {
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
        // See `lift_associated_item_clauses`
        assert!(timpl.type_clauses.is_empty());
        assert!(tdecl.type_clauses.is_empty());

        let args_match = timpl.parent_trait_refs.len() == tdecl.parent_clauses.len()
            && timpl.types.len() == tdecl.types.len()
            && timpl.consts.len() == tdecl.consts.len();
        // Check that type names match.
        let args_match = args_match
            && tdecl
                .types
                .iter()
                .zip(timpl.types.iter())
                .all(|(dname, (iname, _))| dname == iname);
        if !args_match {
            self.error("The generics supplied by the trait impl don't match the trait decl.")
        }
        let methods = timpl.required_methods.len() == tdecl.required_methods.len();
        if !methods {
            self.error("The methods supplied by the trait impl don't match the trait decl.")
        }
    }

    fn visit_llbc_statement(&mut self, st: &Statement) -> ControlFlow<Self::Break> {
        let old_span = self.item_span;
        self.item_span = st.span;
        self.visit_inner(st)?;
        self.item_span = old_span;
        Continue(())
    }
}

pub struct Check;
impl TransformPass for Check {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
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
