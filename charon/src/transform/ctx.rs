use crate::formatter::{FmtCtx, IntoFormatter};
use crate::llbc_ast;
use crate::names::Name;
use crate::pretty::FmtWithCtx;
use crate::translate_ctx::{ErrorCtx, TransOptions, TranslatedCrate};
use crate::ullbc_ast as ast;
use crate::ullbc_ast;
use rustc_error_messages::MultiSpan;
use rustc_hir::def_id::DefId;
use std::fmt;

/// Simpler context used for rustc-independent code transformation. This only depends on rustc for
/// its error reporting machinery.
pub struct TransformCtx<'ctx> {
    /// The options that control translation.
    pub options: TransOptions,
    /// The translated data.
    pub translated: TranslatedCrate,
    /// Context for tracking and reporting errors.
    pub errors: ErrorCtx<'ctx>,
}

/// A pass that transforms the crate data.
pub trait TransformPass: Sync {
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>);
}

/// A pass that modifies ullbc bodies.
pub trait UllbcPass: Sync {
    /// Transform a body.
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, _body: &mut ullbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(&self, ctx: &mut TransformCtx<'_>, decl: &mut ullbc_ast::FunDecl) {
        self.transform_body(ctx, decl.body.as_mut().unwrap())
    }

    /// Transform a global declaration. This forwards to `transform_body` by default.
    fn transform_global(&self, ctx: &mut TransformCtx<'_>, decl: &mut ullbc_ast::GlobalDecl) {
        self.transform_body(ctx, decl.body.as_mut().unwrap())
    }

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }

    /// Log that the pass is about to be run on this body.
    fn log_before_body(&self, ctx: &TransformCtx<'_>, name: &Name, body: &ullbc_ast::ExprBody) {
        let fmt_ctx = &ctx.into_fmt();
        trace!(
            "# About to run pass [{}] on `{}`:\n{}",
            self.name(),
            name.with_ctx(fmt_ctx),
            body.with_ctx(fmt_ctx),
        );
    }
}

/// A pass that modifies llbc bodies.
pub trait LlbcPass: Sync {
    /// Transform a body.
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, _body: &mut llbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(&self, ctx: &mut TransformCtx<'_>, decl: &mut llbc_ast::FunDecl) {
        self.transform_body(ctx, decl.body.as_mut().unwrap())
    }

    /// Transform a global declaration. This forwards to `transform_body` by default.
    fn transform_global(&self, ctx: &mut TransformCtx<'_>, decl: &mut llbc_ast::GlobalDecl) {
        self.transform_body(ctx, decl.body.as_mut().unwrap())
    }

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }

    /// Log that the pass is about to be run on this body.
    fn log_before_body(&self, ctx: &TransformCtx<'_>, name: &Name, body: &llbc_ast::ExprBody) {
        let fmt_ctx = &ctx.into_fmt();
        trace!(
            "# About to run pass [{}] on `{}`:\n{}",
            self.name(),
            name.with_ctx(fmt_ctx),
            body.with_ctx(fmt_ctx),
        );
    }
}

impl TransformPass for dyn UllbcPass {
    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
        ctx.with_mut_unstructured_fun_decls(|ctx, fun_decls| {
            for decl in fun_decls.iter_mut() {
                if let Some(body) = &decl.body {
                    self.log_before_body(ctx, &decl.name, body);
                    ctx.with_def_id(decl.rust_id, |ctx| {
                        self.transform_function(ctx, decl);
                    })
                }
            }
        });
        ctx.with_mut_unstructured_global_decls(|ctx, global_decls| {
            for decl in global_decls.iter_mut() {
                if let Some(body) = &decl.body {
                    self.log_before_body(ctx, &decl.name, body);
                    ctx.with_def_id(decl.rust_id, |ctx| {
                        self.transform_global(ctx, decl);
                    })
                }
            }
        });
    }
}

impl TransformPass for dyn LlbcPass {
    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
        ctx.with_mut_structured_fun_decls(|ctx, fun_decls| {
            for decl in fun_decls.iter_mut() {
                if let Some(body) = &decl.body {
                    self.log_before_body(ctx, &decl.name, body);
                    ctx.with_def_id(decl.rust_id, |ctx| {
                        self.transform_function(ctx, decl);
                    })
                }
            }
        });
        ctx.with_mut_structured_global_decls(|ctx, global_decls| {
            for decl in global_decls.iter_mut() {
                if let Some(body) = &decl.body {
                    self.log_before_body(ctx, &decl.name, body);
                    ctx.with_def_id(decl.rust_id, |ctx| {
                        self.transform_global(ctx, decl);
                    })
                }
            }
        });
    }
}

impl<'ctx> TransformCtx<'ctx> {
    pub(crate) fn continue_on_failure(&self) -> bool {
        self.errors.continue_on_failure()
    }
    pub(crate) fn has_errors(&self) -> bool {
        self.errors.has_errors()
    }

    /// Span an error and register the error.
    pub(crate) fn span_err<S: Into<MultiSpan>>(&mut self, span: S, msg: &str) {
        self.errors.span_err(span, msg)
    }

    pub(crate) fn with_def_id<F, T>(&mut self, def_id: DefId, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let current_def_id = self.errors.def_id;
        self.errors.def_id = Some(def_id);
        let ret = f(self);
        self.errors.def_id = current_def_id;
        ret
    }

    /// Get mutable access to both the ctx and the function declarations.
    pub(crate) fn with_mut_unstructured_fun_decls<R>(
        &mut self,
        f: impl FnOnce(&mut Self, &mut ast::FunDecls) -> R,
    ) -> R {
        let mut fun_decls = std::mem::take(&mut self.translated.fun_decls);
        let ret = f(self, &mut fun_decls);
        self.translated.fun_decls = fun_decls;
        ret
    }
    /// Get mutable access to both the ctx and the global declarations.
    pub(crate) fn with_mut_unstructured_global_decls<R>(
        &mut self,
        f: impl FnOnce(&mut Self, &mut ast::GlobalDecls) -> R,
    ) -> R {
        let mut global_decls = std::mem::take(&mut self.translated.global_decls);
        let ret = f(self, &mut global_decls);
        self.translated.global_decls = global_decls;
        ret
    }
    /// Get mutable access to both the ctx and the function declarations.
    pub(crate) fn with_mut_structured_fun_decls<R>(
        &mut self,
        f: impl FnOnce(&mut Self, &mut llbc_ast::FunDecls) -> R,
    ) -> R {
        let mut fun_decls = std::mem::take(&mut self.translated.structured_fun_decls);
        let ret = f(self, &mut fun_decls);
        self.translated.structured_fun_decls = fun_decls;
        ret
    }
    /// Get mutable access to both the ctx and the global declarations.
    pub(crate) fn with_mut_structured_global_decls<R>(
        &mut self,
        f: impl FnOnce(&mut Self, &mut llbc_ast::GlobalDecls) -> R,
    ) -> R {
        let mut global_decls = std::mem::take(&mut self.translated.structured_global_decls);
        let ret = f(self, &mut global_decls);
        self.translated.structured_global_decls = global_decls;
        ret
    }
}

impl<'a> IntoFormatter for &'a TransformCtx<'_> {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        self.translated.into_fmt()
    }
}

impl fmt::Display for TransformCtx<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt_with_ullbc_defs(f)
    }
}
