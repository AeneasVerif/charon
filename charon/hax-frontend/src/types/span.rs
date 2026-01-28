use crate::prelude::*;
use crate::sinto_todo;
pub use rustc_span::Span;

impl<'tcx, S: BaseState<'tcx>> SInto<S, Span> for Span {
    fn sinto(&self, _s: &S) -> Span {
        *self
    }
}

/// Reflects [`rustc_span::source_map::Spanned`]
#[derive(Clone, Debug)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<'s, S: UnderOwnerState<'s>, T: SInto<S, U>, U> SInto<S, Spanned<U>>
    for rustc_span::source_map::Spanned<T>
{
    fn sinto<'a>(&self, s: &S) -> Spanned<U> {
        Spanned {
            node: self.node.sinto(s),
            span: self.span.sinto(s),
        }
    }
}

sinto_todo!(rustc_span, ErrorGuaranteed);
