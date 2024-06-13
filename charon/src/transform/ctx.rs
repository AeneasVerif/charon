use crate::formatter::{FmtCtx, IntoFormatter};
use crate::gast::{Body, BodyId, FunDecl, FunDeclId, GlobalDecl, GlobalDeclId, Opaque};
use crate::ids::Vector;
use crate::llbc_ast;
use crate::names::Name;
use crate::pretty::FmtWithCtx;
use crate::translate_ctx::{ErrorCtx, TransOptions, TranslatedCrate};
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

/// A pass that modifies ullbc bodies.
pub trait UllbcPass: Sync {
    /// Transform a body.
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, _body: &mut ullbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(
        &self,
        ctx: &mut TransformCtx<'_>,
        _decl: &mut FunDecl,
        body: Result<&mut ullbc_ast::ExprBody, Opaque>,
    ) {
        if let Ok(body) = body {
            self.transform_body(ctx, body)
        }
    }

    /// Transform a global declaration. This forwards to `transform_body` by default.
    fn transform_global(
        &self,
        ctx: &mut TransformCtx<'_>,
        _decl: &mut GlobalDecl,
        body: Result<&mut ullbc_ast::ExprBody, Opaque>,
    ) {
        if let Ok(body) = body {
            self.transform_body(ctx, body)
        }
    }

    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
        ctx.for_each_fun_decl(|ctx, decl, body| {
            let body = body.map(|body| body.as_unstructured_mut().unwrap());
            self.log_before_body(ctx, &decl.name, body.as_deref());
            self.transform_function(ctx, decl, body);
        });
        ctx.for_each_global_decl(|ctx, decl, body| {
            let body = body.map(|body| body.as_unstructured_mut().unwrap());
            self.log_before_body(ctx, &decl.name, body.as_deref());
            self.transform_global(ctx, decl, body);
        });
    }

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }

    /// Log that the pass is about to be run on this body.
    fn log_before_body(
        &self,
        ctx: &TransformCtx<'_>,
        name: &Name,
        body: Result<&ullbc_ast::ExprBody, &Opaque>,
    ) {
        let fmt_ctx = &ctx.into_fmt();
        let body_str = if let Ok(body) = body {
            body.fmt_with_ctx(fmt_ctx)
        } else {
            "<opaque>".to_owned()
        };
        trace!(
            "# About to run pass [{}] on `{}`:\n{}",
            self.name(),
            name.with_ctx(fmt_ctx),
            body_str,
        );
    }
}

/// A pass that modifies llbc bodies.
pub trait LlbcPass: Sync {
    /// Transform a body.
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, _body: &mut llbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(
        &self,
        ctx: &mut TransformCtx<'_>,
        _decl: &mut FunDecl,
        body: Result<&mut llbc_ast::ExprBody, Opaque>,
    ) {
        if let Ok(body) = body {
            self.transform_body(ctx, body)
        }
    }

    /// Transform a global declaration. This forwards to `transform_body` by default.
    fn transform_global(
        &self,
        ctx: &mut TransformCtx<'_>,
        _decl: &mut GlobalDecl,
        body: Result<&mut llbc_ast::ExprBody, Opaque>,
    ) {
        if let Ok(body) = body {
            self.transform_body(ctx, body)
        }
    }

    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
        ctx.for_each_fun_decl(|ctx, decl, body| {
            let body = body.map(|body| body.as_structured_mut().unwrap());
            self.log_before_body(ctx, &decl.name, body.as_deref());
            self.transform_function(ctx, decl, body);
        });
        ctx.for_each_global_decl(|ctx, decl, body| {
            let body = body.map(|body| body.as_structured_mut().unwrap());
            self.log_before_body(ctx, &decl.name, body.as_deref());
            self.transform_global(ctx, decl, body);
        });
    }

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }

    /// Log that the pass is about to be run on this body.
    fn log_before_body(
        &self,
        ctx: &TransformCtx<'_>,
        name: &Name,
        body: Result<&llbc_ast::ExprBody, &Opaque>,
    ) {
        let fmt_ctx = &ctx.into_fmt();
        let body_str = if let Ok(body) = body {
            body.fmt_with_ctx(fmt_ctx)
        } else {
            "<opaque>".to_owned()
        };
        trace!(
            "# About to run pass [{}] on `{}`:\n{}",
            self.name(),
            name.with_ctx(fmt_ctx),
            body_str,
        );
    }
}

/// A pass that transforms the crate data.
pub trait TransformPass: Sync {
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>);
}

impl TransformPass for dyn UllbcPass {
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
        self.transform_ctx(ctx)
    }
}

impl TransformPass for dyn LlbcPass {
    fn transform_ctx(&self, ctx: &mut TransformCtx<'_>) {
        self.transform_ctx(ctx)
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

    /// Get mutable access to both the ctx and the bodies.
    pub(crate) fn with_mut_bodies<R>(
        &mut self,
        f: impl FnOnce(&mut Self, &mut Vector<BodyId, Body>) -> R,
    ) -> R {
        let mut bodies = std::mem::take(&mut self.translated.bodies);
        let ret = f(self, &mut bodies);
        self.translated.bodies = bodies;
        ret
    }
    /// Get mutable access to both the ctx and the function declarations.
    pub(crate) fn with_mut_fun_decls<R>(
        &mut self,
        f: impl FnOnce(&mut Self, &mut Vector<FunDeclId, FunDecl>) -> R,
    ) -> R {
        let mut fun_decls = std::mem::take(&mut self.translated.fun_decls);
        let ret = f(self, &mut fun_decls);
        self.translated.fun_decls = fun_decls;
        ret
    }
    /// Get mutable access to both the ctx and the global declarations.
    pub(crate) fn with_mut_global_decls<R>(
        &mut self,
        f: impl FnOnce(&mut Self, &mut Vector<GlobalDeclId, GlobalDecl>) -> R,
    ) -> R {
        let mut global_decls = std::mem::take(&mut self.translated.global_decls);
        let ret = f(self, &mut global_decls);
        self.translated.global_decls = global_decls;
        ret
    }

    /// Mutably iterate over the bodies.
    // FIXME: this does not set `with_def_id` to track error sources. That would require having a
    // way to go from the body back to its parent declaration.
    pub(crate) fn for_each_body(&mut self, mut f: impl FnMut(&mut Self, &mut Body)) {
        self.with_mut_bodies(|ctx, bodies| {
            for body in bodies {
                f(ctx, body)
            }
        })
    }
    pub(crate) fn for_each_structured_body(
        &mut self,
        mut f: impl FnMut(&mut Self, &mut llbc_ast::ExprBody),
    ) {
        self.for_each_body(|ctx, body| f(ctx, body.as_structured_mut().unwrap()))
    }

    /// Mutably iterate over the function declarations without errors.
    pub(crate) fn for_each_fun_decl(
        &mut self,
        mut f: impl FnMut(&mut Self, &mut FunDecl, Result<&mut Body, Opaque>),
    ) {
        self.with_mut_bodies(|ctx, bodies| {
            ctx.with_mut_fun_decls(|ctx, decls| {
                for decl in decls.iter_mut() {
                    let body = match decl.body {
                        Ok(id) => {
                            match bodies.get_mut(id) {
                                Some(body) => Ok(body),
                                // This body has errored, we skip the item.
                                None => continue,
                            }
                        }
                        Err(Opaque) => Err(Opaque),
                    };
                    ctx.with_def_id(decl.rust_id, |ctx| {
                        f(ctx, decl, body);
                    })
                }
            })
        })
    }

    /// Mutably iterate over the global declarations without errors.
    pub(crate) fn for_each_global_decl(
        &mut self,
        mut f: impl FnMut(&mut Self, &mut GlobalDecl, Result<&mut Body, Opaque>),
    ) {
        self.with_mut_bodies(|ctx, bodies| {
            ctx.with_mut_global_decls(|ctx, decls| {
                for decl in decls.iter_mut() {
                    let body = match decl.body {
                        Ok(id) => {
                            match bodies.get_mut(id) {
                                Some(body) => Ok(body),
                                // This body has errored, we skip the item.
                                None => continue,
                            }
                        }
                        Err(Opaque) => Err(Opaque),
                    };
                    ctx.with_def_id(decl.rust_id, |ctx| {
                        f(ctx, decl, body);
                    })
                }
            })
        })
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
        self.translated.fmt(f)
    }
}
