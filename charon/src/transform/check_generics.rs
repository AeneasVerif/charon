//! Check that all supplied generic types match the corresponding generic parameters.
use derive_generic_visitor::*;
use index_vec::Idx;
use itertools::Itertools;
use std::{borrow::Cow, fmt::Display, mem};

use crate::{
    ast::*,
    formatter::{FmtCtx, IntoFormatter, PushBinder},
    pretty::FmtWithCtx,
    register_error,
};

use super::{ctx::TransformPass, TransformCtx};

#[derive(Visitor)]
struct CheckGenericsVisitor<'a> {
    ctx: &'a TransformCtx,
    // For pretty error printing. This can print values that we encounter because we track binders
    // properly. This doesn't have the right binders to print values we get from somewhere else
    // (namely `GenericParam`s).
    val_fmt_ctx: FmtCtx<'a>,
    phase: &'static str,
    // Tracks an enclosing span to make errors useful.
    span: Span,
    /// Remember the names of the types visited up to here.
    visit_stack: Vec<&'static str>,
}

impl CheckGenericsVisitor<'_> {
    fn error(&self, message: impl Display) {
        register_error!(
            self.ctx,
            self.span,
            "Found inconsistent generics {}:\n{message}\nVisitor stack:\n  {}",
            self.phase,
            self.visit_stack.iter().rev().join("\n  ")
        );
    }

    fn zip_assert_match<I, A, B, FmtA, FmtB>(
        &self,
        a: &Vector<I, A>,
        b: &Vector<I, B>,
        a_fmt: &FmtA,
        b_fmt: &FmtB,
        kind: &str,
        check_inner: impl Fn(&A, &B),
    ) where
        I: Idx,
        A: for<'a> FmtWithCtx<FmtA>,
        B: for<'a> FmtWithCtx<FmtB>,
    {
        if a.len() == b.len() {
            a.iter().zip(b.iter()).for_each(|(x, y)| check_inner(x, y));
        } else {
            let a = a.iter().map(|x| x.fmt_with_ctx(a_fmt)).join(", ");
            let b = b.iter().map(|x| x.fmt_with_ctx(b_fmt)).join(", ");
            self.error(format!(
                "Mismatched {kind}:\
                \nexpected: [{a}]\
                \n     got: [{b}]"
            ))
        }
    }

    fn assert_clause_matches(
        &self,
        params_fmt: &FmtCtx<'_>,
        tclause: &TraitClause,
        tref: &TraitRef,
    ) {
        let clause_trait_id = tclause.trait_.skip_binder.trait_id;
        let ref_trait_id = tref.trait_decl_ref.skip_binder.trait_id;
        if clause_trait_id != ref_trait_id {
            let tclause = tclause.fmt_with_ctx(params_fmt);
            let tref_pred = tref.trait_decl_ref.fmt_with_ctx(&self.val_fmt_ctx);
            let tref = tref.fmt_with_ctx(&self.val_fmt_ctx);
            self.error(format!(
                "Mismatched trait clause:\
                \nexpected: {tclause}\
                \n     got: {tref}: {tref_pred}"
            ));
        }
    }

    fn assert_matches(&self, params_fmt: &FmtCtx<'_>, params: &GenericParams, args: &GenericArgs) {
        self.zip_assert_match(
            &params.regions,
            &args.regions,
            params_fmt,
            &self.val_fmt_ctx,
            "regions",
            |_, _| {},
        );
        self.zip_assert_match(
            &params.types,
            &args.types,
            params_fmt,
            &self.val_fmt_ctx,
            "type generics",
            |_, _| {},
        );
        self.zip_assert_match(
            &params.const_generics,
            &args.const_generics,
            params_fmt,
            &self.val_fmt_ctx,
            "const generics",
            |_, _| {},
        );
        self.zip_assert_match(
            &params.trait_clauses,
            &args.trait_refs,
            params_fmt,
            &self.val_fmt_ctx,
            "trait clauses",
            |tclause, tref| self.assert_clause_matches(params_fmt, tclause, tref),
        );
    }
}

impl VisitAst for CheckGenericsVisitor<'_> {
    fn visit<'a, T: AstVisitable>(&'a mut self, x: &T) -> ControlFlow<Self::Break> {
        self.visit_stack.push(x.name());
        x.drive(self)?; // default behavior
        self.visit_stack.pop();
        Continue(())
    }

    fn visit_binder<T: AstVisitable>(&mut self, binder: &Binder<T>) -> ControlFlow<Self::Break> {
        let new_fmt_ctx = self.val_fmt_ctx.push_binder(Cow::Borrowed(&binder.params));
        // Build a new `self` with a shorter `'a` because the new `'a` borrows from `binder`.
        let mut new_this = CheckGenericsVisitor {
            ctx: self.ctx,
            val_fmt_ctx: new_fmt_ctx,
            phase: self.phase,
            span: self.span,
            visit_stack: mem::take(&mut self.visit_stack),
        };
        new_this.visit_inner(binder)?;
        self.visit_stack = new_this.visit_stack;
        Continue(())
    }

    fn visit_region_binder<T: AstVisitable>(
        &mut self,
        binder: &RegionBinder<T>,
    ) -> ControlFlow<Self::Break> {
        let new_fmt_ctx = self.val_fmt_ctx.push_bound_regions(&binder.regions);
        // Build a new `self` with a shorter `'a` because the new `'a` borrows from `binder`.
        let mut new_this = CheckGenericsVisitor {
            ctx: self.ctx,
            val_fmt_ctx: new_fmt_ctx,
            phase: self.phase,
            span: self.span,
            visit_stack: mem::take(&mut self.visit_stack),
        };
        new_this.visit_inner(binder)?;
        self.visit_stack = new_this.visit_stack;
        Continue(())
    }

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
        let fmt1;
        let fmt2;
        let (params, params_fmt) = match &args.target {
            GenericsSource::Item(item_id) => {
                let Some(item) = self.ctx.translated.get_item(*item_id) else {
                    return;
                };
                let params = item.generic_params();
                fmt1 = self.ctx.into_fmt();
                let fmt = fmt1.push_binder(Cow::Borrowed(params));
                (params, fmt)
            }
            GenericsSource::Method(trait_id, method_name) => {
                let Some(trait_decl) = self.ctx.translated.trait_decls.get(*trait_id) else {
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
                let params = &bound_fn.params;
                fmt1 = self.ctx.into_fmt();
                fmt2 = fmt1.push_binder(Cow::Borrowed(&trait_decl.generics));
                let fmt = fmt2.push_binder(Cow::Borrowed(params));
                (params, fmt)
            }
            GenericsSource::Builtin => return,
        };
        self.assert_matches(&params_fmt, params, args);
    }

    // Special case that is not represented as a `GenericArgs`.
    fn enter_trait_impl(&mut self, timpl: &TraitImpl) {
        let Some(tdecl) = self
            .ctx
            .translated
            .trait_decls
            .get(timpl.impl_trait.trait_id)
        else {
            return;
        };
        // See `lift_associated_item_clauses`
        assert!(timpl.type_clauses.is_empty());
        assert!(tdecl.type_clauses.is_empty());

        let fmt1 = self.ctx.into_fmt();
        let tdecl_fmt = fmt1.push_binder(Cow::Borrowed(&tdecl.generics));
        self.zip_assert_match(
            &tdecl.parent_clauses,
            &timpl.parent_trait_refs,
            &tdecl_fmt,
            &self.val_fmt_ctx,
            "trait parent clauses",
            |tclause, tref| self.assert_clause_matches(&tdecl_fmt, tclause, tref),
        );
        let types_match = timpl.types.len() == tdecl.types.len()
            && tdecl
                .types
                .iter()
                .zip(timpl.types.iter())
                .all(|(dname, (iname, _))| dname == iname);
        if !types_match {
            self.error(
                "The associated types supplied by the trait impl don't match the trait decl.",
            )
        }
        let consts_match = timpl.consts.len() == tdecl.consts.len()
            && tdecl
                .types
                .iter()
                .zip(timpl.types.iter())
                .all(|(dname, (iname, _))| dname == iname);
        if !consts_match {
            self.error(
                "The associated consts supplied by the trait impl don't match the trait decl.",
            )
        }
        let methods = timpl.required_methods.len() == tdecl.required_methods.len();
        if !methods {
            self.error("The methods supplied by the trait impl don't match the trait decl.")
        }
    }

    fn visit_ullbc_statement(&mut self, st: &ullbc_ast::Statement) -> ControlFlow<Self::Break> {
        // Track span for more precise error messages.
        let old_span = self.span;
        self.span = st.span;
        self.visit_inner(st)?;
        self.span = old_span;
        Continue(())
    }

    fn visit_llbc_statement(&mut self, st: &llbc_ast::Statement) -> ControlFlow<Self::Break> {
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
                ctx,
                val_fmt_ctx: ctx.into_fmt(),
                phase: self.0,
                span: item.item_meta().span,
                visit_stack: Default::default(),
            };
            item.drive(&mut visitor);
        }
    }
}
