mod adt;
mod def_id;
mod mir;
mod new;
mod predicates;
mod traits;
mod ty;
mod vars;

pub use adt::*;
pub use def_id::*;
pub use mir::*;
pub use new::*;
pub use predicates::*;
pub use traits::*;
pub use ty::*;
pub use vars::*;

use crate::hax::prelude::*;
use crate::hax::sinto_todo;

sinto_reexport!(rustc_span::Span);

pub use rustc_span::Spanned;
impl<'s, S: UnderOwnerState<'s>, T: SInto<S, U>, U> SInto<S, Spanned<U>> for Spanned<T> {
    fn sinto<'a>(&self, s: &S) -> Spanned<U> {
        Spanned {
            node: self.node.sinto(s),
            span: self.span,
        }
    }
}

sinto_todo!(rustc_span, ErrorGuaranteed);

/// Reflects [`rustc_span::symbol::Ident`]
pub type Ident = (Symbol, Span);
impl<'tcx, S: BaseState<'tcx>> SInto<S, Ident> for rustc_span::symbol::Ident {
    fn sinto(&self, s: &S) -> Ident {
        (self.name.sinto(s), self.span.sinto(s))
    }
}
