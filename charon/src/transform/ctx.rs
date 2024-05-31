use crate::formatter::{FmtCtx, IntoFormatter};
use crate::gast::*;
use crate::llbc_ast;
use crate::names::Name;
use crate::translate_ctx::{ErrorCtx, TransOptions, TranslatedCrate};
use crate::ullbc_ast as ast;
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

    pub(crate) fn iter_unstructured_bodies<F>(&mut self, f: F)
    where
        F: Fn(&mut Self, &Name, &mut ast::ExprBody),
    {
        self.with_mut_unstructured_fun_decls(|ctx, fun_decls| {
            ctx.with_mut_unstructured_global_decls(|ctx, global_decls| {
                let bodies: Vec<_> = iter_function_bodies(fun_decls)
                    .chain(iter_global_bodies(global_decls))
                    .collect();
                for (id, name, b) in bodies {
                    ctx.with_def_id(id, |ctx| f(ctx, name, b))
                }
            })
        })
    }

    pub(crate) fn iter_structured_bodies<F>(&mut self, f: F)
    where
        F: Fn(&mut Self, &Name, &mut llbc_ast::ExprBody),
    {
        self.with_mut_structured_fun_decls(|ctx, fun_decls| {
            ctx.with_mut_structured_global_decls(|ctx, global_decls| {
                let bodies: Vec<_> = iter_function_bodies(fun_decls)
                    .chain(iter_global_bodies(global_decls))
                    .collect();
                for (id, name, b) in bodies {
                    ctx.with_def_id(id, |ctx| f(ctx, name, b))
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
        self.translated.fmt_with_ullbc_defs(f)
    }
}
