//! Copies of the relevant `HIR` types. HIR represents the code of a rust crate post-macro
//! expansion. It is close to the parsed AST, modulo some desugarings (and macro expansion).
//!
//! This module also includes some `rustc_ast` definitions when they show up in HIR.
use crate::prelude::*;
use crate::sinto_todo;

use rustc_ast::ast;
use rustc_hir as hir;

/// Reflects [`ast::LitFloatType`]

#[derive(AdtInto, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ast::LitFloatType, state: S as gstate)]
pub enum LitFloatType {
    Suffixed(FloatTy),
    Unsuffixed,
}

impl<S> SInto<S, Mutability> for hir::Mutability {
    fn sinto(&self, _s: &S) -> Mutability {
        match self {
            Self::Mut => true,
            Self::Not => false,
        }
    }
}

impl<'x: 'tcx, 'tcx, S: UnderOwnerState<'tcx>> SInto<S, Ty> for hir::Ty<'x> {
    fn sinto(self: &hir::Ty<'x>, s: &S) -> Ty {
        // **Important:**
        // We need a local id here, and we get it from the owner id, which must
        // be local. It is safe to do so, because if we have access to a HIR ty,
        // it necessarily means we are exploring a local item (we don't have
        // access to the HIR of external objects, only their MIR).
        rustc_hir_analysis::lower_ty(s.base().tcx, self).sinto(s)
    }
}

/// Reflects [`rustc_ast::tokenstream::TokenStream`] as a plain
/// string. If you need to reshape that into Rust tokens or construct,
/// please use, e.g., `syn`.
pub type TokenStream = String;

impl<'t, S> SInto<S, TokenStream> for rustc_ast::tokenstream::TokenStream {
    fn sinto(&self, _: &S) -> String {
        rustc_ast_pretty::pprust::tts_to_string(self)
    }
}

/// Reflects [`rustc_ast::token::Delimiter`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::Delimiter, state: S as _s)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
    Invisible(InvisibleOrigin),
}

sinto_todo!(rustc_ast::token, InvisibleOrigin);

/// Reflects [`rustc_ast::ast::DelimArgs`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::DelimArgs, state: S as gstate)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DelimArgs {
    pub dspan: DelimSpan,
    pub delim: Delimiter,
    pub tokens: TokenStream,
}

sinto_todo!(rustc_ast::tokenstream, DelimSpan);

/// Reflects [`rustc_span::symbol::Ident`]
pub type Ident = (Symbol, Span);

impl<'tcx, S: BaseState<'tcx>> SInto<S, Ident> for rustc_span::symbol::Ident {
    fn sinto(&self, s: &S) -> Ident {
        (self.name.sinto(s), self.span.sinto(s))
    }
}

/// Reflects [`rustc_ast::AttrStyle`]

#[derive(AdtInto, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<S>, from: rustc_ast::AttrStyle, state: S as _s)]
pub enum AttrStyle {
    Outer,
    Inner,
}

/// Reflects [`rustc_ast::ast::StrStyle`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::ast::StrStyle, state: S as gstate)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum StrStyle {
    Cooked,
    Raw(u8),
}

/// Reflects [`rustc_ast::ast::LitKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::LitKind, state: S as gstate)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum LitKind {
    Str(Symbol, StrStyle),
    ByteStr(ByteSymbol, StrStyle),
    CStr(ByteSymbol, StrStyle),
    Byte(u8),
    Char(char),
    Int(u128, LitIntType),
    Float(Symbol, LitFloatType),
    Bool(bool),
    Err(ErrorGuaranteed),
}

impl<S> SInto<S, u128> for rustc_data_structures::packed::Pu128 {
    fn sinto(&self, _s: &S) -> u128 {
        self.0
    }
}

/// Reflects [`rustc_ast::token::CommentKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_ast::token::CommentKind, state: S as _s)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum CommentKind {
    Line,
    Block,
}

/// Reflects [`rustc_hir::AttrArgs`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::AttrArgs, state: S as tcx)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AttrArgs {
    Empty,
    Delimited(DelimArgs),
    Eq { eq_span: Span, expr: MetaItemLit },
}

/// Reflects [`rustc_ast::MetaItemLit`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::MetaItemLit, state: S as tcx)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MetaItemLit {
    pub symbol: Symbol,
    pub suffix: Option<Symbol>,
    pub kind: LitKind,
    pub span: Span,
}

/// Reflects [`rustc_hir::AttrItem`]

#[derive(AdtInto, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::AttrItem, state: S as gstate)]
pub struct AttrItem {
    #[map(x.to_string())]
    pub path: String,
    pub args: AttrArgs,
    pub span: Span,
}

impl<S> SInto<S, String> for rustc_ast::tokenstream::LazyAttrTokenStream {
    fn sinto(&self, st: &S) -> String {
        rustc_ast::tokenstream::TokenStream::new(self.to_attr_token_stream().to_token_trees())
            .sinto(st)
    }
}

sinto_todo!(rustc_hir, GenericArgs<'a> as HirGenericArgs);
sinto_todo!(rustc_hir, InlineAsm<'a>);
sinto_todo!(rustc_hir, MissingLifetimeKind);
sinto_todo!(rustc_hir, QPath<'tcx>);
sinto_todo!(rustc_hir, WhereRegionPredicate<'tcx>);
sinto_todo!(rustc_hir, WhereEqPredicate<'tcx>);
sinto_todo!(rustc_hir, OwnerId);
