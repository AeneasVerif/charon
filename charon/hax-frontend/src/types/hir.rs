//! Copies of the relevant `HIR` types. HIR represents the code of a rust crate post-macro
//! expansion. It is close to the parsed AST, modulo some desugarings (and macro expansion).
//!
//! This module also includes some `rustc_ast` definitions when they show up in HIR.
use crate::prelude::*;

/// Reflects [`rustc_span::symbol::Ident`]
pub type Ident = (Symbol, Span);

impl<'tcx, S: BaseState<'tcx>> SInto<S, Ident> for rustc_span::symbol::Ident {
    fn sinto(&self, s: &S) -> Ident {
        (self.name.sinto(s), self.span.sinto(s))
    }
}

/// Reflects [`rustc_hir::attrs::InlineAttr`]
#[derive(AdtInto, Clone, Debug, Hash, PartialEq, Eq)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::attrs::InlineAttr, state: S as _s)]
pub enum InlineAttr {
    None,
    Hint,
    Always,
    Never,
    Force {
        attr_span: Span,
        reason: Option<Symbol>,
    },
}
