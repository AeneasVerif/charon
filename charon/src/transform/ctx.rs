use crate::ast::*;
use crate::errors::ErrorCtx;
use crate::formatter::{FmtCtx, IntoFormatter};
use crate::llbc_ast;
use crate::name_matcher::NamePattern;
use crate::pretty::FmtWithCtx;
use crate::ullbc_ast;
use std::{fmt, mem};

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
    /// Print the llbc just after control-flow reconstruction.
    pub print_built_llbc: bool,
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
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        if let Ok(body) = &mut decl.body {
            self.transform_body(ctx, body.as_unstructured_mut().unwrap())
        }
    }

    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|ctx, decl| {
            let body = decl
                .body
                .as_mut()
                .map(|body| body.as_unstructured_mut().unwrap())
                .map_err(|opaque| *opaque);
            self.log_before_body(ctx, &decl.item_meta.name, body.as_deref());
            self.transform_function(ctx, decl);
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
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        if let Ok(body) = &mut decl.body {
            self.transform_body(ctx, body.as_structured_mut().unwrap())
        }
    }

    /// Transform the given context. This forwards to the other methods by default.
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|ctx, decl| {
            let body = decl
                .body
                .as_mut()
                .map(|body| body.as_structured_mut().unwrap())
                .map_err(|opaque| *opaque);
            self.log_before_body(ctx, &decl.item_meta.name, body.as_deref());
            self.transform_function(ctx, decl);
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

    /// Mutably iterate over the bodies.
    /// Warning: we replace each body with `Err(Opaque)` while inspecting it so we can keep access
    /// to the rest of the crate.
    pub(crate) fn for_each_body(&mut self, mut f: impl FnMut(&mut Self, &mut Body)) {
        let fn_ids = self.translated.fun_decls.all_indices();
        for id in fn_ids {
            if let Some(decl) = self.translated.fun_decls.get_mut(id) {
                if let Ok(mut body) = mem::replace(&mut decl.body, Err(Opaque)) {
                    let fun_decl_id = decl.def_id;
                    let is_local = decl.item_meta.is_local;
                    self.with_def_id(fun_decl_id, is_local, |ctx| f(ctx, &mut body));
                    self.translated.fun_decls[id].body = Ok(body);
                }
            }
        }
    }
    pub(crate) fn for_each_structured_body(
        &mut self,
        mut f: impl FnMut(&mut Self, &mut llbc_ast::ExprBody),
    ) {
        self.for_each_body(|ctx, body| f(ctx, body.as_structured_mut().unwrap()))
    }

    /// Mutably iterate over the function declarations.
    /// Warning: each inspected fundecl becomes inaccessible from `ctx` during the course of this function.
    pub(crate) fn for_each_fun_decl(&mut self, mut f: impl FnMut(&mut Self, &mut FunDecl)) {
        let fn_ids = self.translated.fun_decls.all_indices();
        for id in fn_ids {
            if let Some(mut decl) = self.translated.fun_decls.remove(id) {
                let fun_decl_id = decl.def_id;
                let is_local = decl.item_meta.is_local;
                self.with_def_id(fun_decl_id, is_local, |ctx| f(ctx, &mut decl));
                self.translated.fun_decls.set_slot(id, decl);
            }
        }
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
