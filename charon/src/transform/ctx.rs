use crate::ast::*;
use crate::errors::ErrorCtx;
use crate::formatter::{FmtCtx, IntoFormatter};
use crate::ids::Vector;
use crate::llbc_ast;
use crate::name_matcher::NamePattern;
use crate::pretty::FmtWithCtx;
use crate::ullbc_ast;
use std::fmt;

/// The options that control transformation.
pub struct TransformOptions {
    /// Error out if some code ends up being duplicated by the control-flow
    /// reconstruction (note that because several patterns in a match may lead
    /// to the same branch, it is node always possible not to duplicate code).
    pub no_code_duplication: bool,
    /// Whether to hide the `Sized`, `Sync`, `Send` and `Unpin` marker traits anywhere they show
    /// up.
    pub hide_marker_traits: bool,
    /// Do not merge the chains of gotos.
    pub no_merge_goto_chains: bool,
    /// List of patterns to assign a given opacity to. Same as the corresponding `TranslateOptions`
    /// field.
    pub item_opacities: Vec<(NamePattern, ItemOpacity)>,
}

/// Simpler context used for rustc-independent code transformation. This only depends on rustc for
/// its error reporting machinery.
pub struct TransformCtx {
    /// The options that control transformation.
    pub options: TransformOptions,
    /// The translated data.
    pub translated: TranslatedCrate,
    /// Context for tracking and reporting errors.
    pub errors: ErrorCtx,
}

/// A pass that modifies ullbc bodies.
pub trait UllbcPass: Sync {
    /// Transform a body.
    fn transform_body(&self, _ctx: &mut TransformCtx, _body: &mut ullbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(
        &self,
        ctx: &mut TransformCtx,
        _decl: &mut FunDecl,
        body: Result<&mut ullbc_ast::ExprBody, Opaque>,
    ) {
        if let Ok(body) = body {
            self.transform_body(ctx, body)
        }
    }

    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|ctx, decl, body| {
            let body = body.map(|body| body.as_unstructured_mut().unwrap());
            self.log_before_body(ctx, &decl.item_meta.name, body.as_deref());
            self.transform_function(ctx, decl, body);
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
        ctx: &TransformCtx,
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
    fn transform_body(&self, _ctx: &mut TransformCtx, _body: &mut llbc_ast::ExprBody) {}

    /// Transform a function declaration. This forwards to `transform_body` by default.
    fn transform_function(
        &self,
        ctx: &mut TransformCtx,
        _decl: &mut FunDecl,
        body: Result<&mut llbc_ast::ExprBody, Opaque>,
    ) {
        if let Ok(body) = body {
            self.transform_body(ctx, body)
        }
    }

    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|ctx, decl, body| {
            let body = body.map(|body| body.as_structured_mut().unwrap());
            self.log_before_body(ctx, &decl.item_meta.name, body.as_deref());
            self.transform_function(ctx, decl, body);
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
        ctx: &TransformCtx,
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
    fn transform_ctx(&self, ctx: &mut TransformCtx);

    /// The name of the pass, used for debug logging. The default implementation uses the type
    /// name.
    fn name(&self) -> &str {
        std::any::type_name::<Self>()
    }
}

impl<'ctx> TransformCtx {
    pub(crate) fn continue_on_failure(&self) -> bool {
        self.errors.continue_on_failure()
    }
    pub(crate) fn has_errors(&self) -> bool {
        self.errors.has_errors()
    }

    /// Span an error and register the error.
    pub(crate) fn span_err(&mut self, span: Span, msg: &str) {
        self.errors.span_err(&self.translated, span, msg)
    }

    pub(crate) fn with_def_id<F, T>(
        &mut self,
        def_id: impl Into<AnyTransId>,
        def_id_is_local: bool,
        f: F,
    ) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        let current_def_id = self.errors.def_id;
        let current_def_id_is_local = self.errors.def_id_is_local;
        self.errors.def_id = Some(def_id.into());
        self.errors.def_id_is_local = def_id_is_local;
        let ret = f(self);
        self.errors.def_id = current_def_id;
        self.errors.def_id_is_local = current_def_id_is_local;
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
                    ctx.with_def_id(decl.def_id, decl.item_meta.is_local, |ctx| {
                        f(ctx, decl, body);
                    })
                }
            })
        })
    }
}

impl<'a> IntoFormatter for &'a TransformCtx {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        self.translated.into_fmt()
    }
}

impl fmt::Display for TransformCtx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.translated.fmt(f)
    }
}
