//! Check that all supplied generic types match the corresponding generic parameters.
use derive_generic_visitor::*;
use std::fmt::Display;

use crate::{errors::ErrorCtx, llbc_ast::*, register_error_or_panic};

use super::{ctx::TransformPass, TransformCtx};

#[derive(Visitor)]
struct CheckGenericsVisitor<'a> {
    translated: &'a TranslatedCrate,
    phase: &'static str,
    error_ctx: &'a mut ErrorCtx,
    // Tracks an enclosing span to make errors useful.
    span: Span,
}

impl CheckGenericsVisitor<'_> {
    fn error(&mut self, message: impl Display) {
        let message = format!("Found inconsistent generics {}:\n{message}", self.phase);
        register_error_or_panic!(self.error_ctx, self.translated, self.span, message);
    }
}

impl VisitAst for CheckGenericsVisitor<'_> {
    fn visit_aggregate_kind(&mut self, agg: &AggregateKind) -> ControlFlow<Self::Break> {
        match agg {
            AggregateKind::Adt(..) => self.visit_inner(agg)?,
            AggregateKind::Closure(_id, args) => {
                // TODO(#194): handle closure generics properly
                // This does not visit the args themselves, only their contents, because we mess up
                // closure generics for now.
                self.visit_inner(args)?
            }
            AggregateKind::Array(..) => self.visit_inner(agg)?,
        }
        Continue(())
    }

    fn enter_generic_args(&mut self, args: &GenericArgs) {
        let params = match &args.target {
            GenericsSource::Item(item_id) => {
                let Some(item) = self.translated.get_item(*item_id) else {
                    return;
                };
                item.generic_params()
            }
            GenericsSource::Method(trait_id, method_name) => {
                let Some(trait_decl) = self.translated.trait_decls.get(*trait_id) else {
                    return;
                };
                let Some((_, bound_fn)) = trait_decl
                    .required_methods
                    .iter()
                    .chain(trait_decl.provided_methods.iter())
                    .find(|(n, _)| n == method_name)
                else {
                    return;
                };
                &bound_fn.params
            }
            GenericsSource::Builtin => return,
        };
        if !args.matches(params) {
            self.error(format!(
                "Mismatched generics:\nexpected: {params:?}\n     got: {args:?}"
            ))
        }
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
        // Track span for more precise error messages.
        let old_span = self.span;
        self.span = st.span;
        self.visit_inner(st)?;
        self.span = old_span;
        Continue(())
    }
}

// The argument is a name to disambiguate the two times we run this check.
pub struct Check(pub &'static str);
impl TransformPass for Check {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        for item in ctx.translated.all_items() {
            let mut visitor = CheckGenericsVisitor {
                translated: &ctx.translated,
                error_ctx: &mut ctx.errors,
                phase: self.0,
                span: item.item_meta().span,
            };
            item.drive(&mut visitor);
        }
    }
}
