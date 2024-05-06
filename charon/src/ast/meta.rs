//! Meta-information about programs (spans, etc.).

pub use crate::meta_utils::*;
use macros::{EnumAsGetters, EnumIsA};
use serde::{Deserialize, Serialize};

generate_index_type!(LocalFileId);
generate_index_type!(VirtualFileId);

#[allow(non_snake_case)]
pub mod FileId {
    use crate::meta::*;

    #[derive(
        Debug,
        Clone,
        Copy,
        Hash,
        PartialEq,
        Eq,
        PartialOrd,
        Ord,
        EnumIsA,
        EnumAsGetters,
        Serialize,
        Deserialize,
    )]
    pub enum Id {
        LocalId(LocalFileId::Id),
        VirtualId(VirtualFileId::Id),
    }
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub struct Loc {
    /// The (1-based) line number.
    pub line: usize,
    /// The (0-based) column offset.
    pub col: usize,
}

/// For use when deserializing.
fn dummy_span_data() -> rustc_span::SpanData {
    rustc_span::DUMMY_SP.data()
}

/// Span information
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub struct Span {
    pub file_id: FileId::Id,
    pub beg: Loc,
    pub end: Loc,
    /// We keep the rust span so as to be able to leverage Rustc to print
    /// error messages (useful in the micro-passes for instance).
    /// We use `Span` instead of `SpanData` because `Span` is not `Send` when rustc runs
    /// single-threaded (default on older versions). We need this to be `Send` because we pass this
    /// data out of the rustc callbacks in charon-driver.
    #[serde(skip)]
    #[serde(default = "dummy_span_data")]
    pub rust_span_data: rustc_span::SpanData,
}

impl From<Span> for rustc_error_messages::MultiSpan {
    fn from(span: Span) -> Self {
        span.rust_span_data.span().into()
    }
}

/// Meta information about a piece of code (block, statement, etc.)
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub struct Meta {
    /// The source code span.
    ///
    /// If this meta information is for a statement/terminator coming from a macro
    /// expansion/inlining/etc., this span is (in case of macros) for the macro
    /// before expansion (i.e., the location the code where the user wrote the call
    /// to the macro).
    ///
    /// Ex:
    /// ```text
    /// // Below, we consider the spans for the statements inside `test`
    ///
    /// //   the statement we consider, which gets inlined in `test`
    ///                          VV
    /// macro_rules! macro { ... st ... } // `generated_from_span` refers to this location
    ///
    /// fn test() {
    ///     macro!(); // <-- `span` refers to this location
    /// }
    /// ```
    pub span: Span,
    /// Where the code actually comes from, in case of macro expansion/inlining/etc.
    pub generated_from_span: Option<Span>,
}

impl From<Meta> for rustc_error_messages::MultiSpan {
    fn from(meta: Meta) -> Self {
        meta.span.into()
    }
}

/// Attributes (`#[...]`). For now we store just the string representation.
pub type Attribute = String;

/// `#[inline]` built-in attribute.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum InlineAttr {
    /// `#[inline]`
    Hint,
    /// `#[inline(never)]`
    Never,
    /// `#[inline(always)]`
    Always,
}

/// Meta information about an item (function, trait decl, trait impl, type decl, global).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ItemMeta {
    pub meta: Meta,
    /// Attributes (`#[...]`).
    pub attributes: Vec<Attribute>,
    /// Inline hints (on functions only).
    pub inline: Option<InlineAttr>,
    /// Whether this item is declared public. Impl blocks and closures don't have visibility
    /// modifiers; we arbitrarily set this to `false` for them.
    ///
    /// Note that this is different from being part of the crate's public API: to be part of the
    /// public API, an item has to also be reachable from public items in the crate root. For
    /// example:
    /// ```rust,ignore
    /// mod foo {
    ///     pub struct X;
    /// }
    /// mod bar {
    ///     pub fn something(_x: super::foo::X) {}
    /// }
    /// pub use bar::something; // exposes `X`
    /// ```
    /// Without the `pub use ...`, neither `X` nor `something` would be part of the crate's public
    /// API (this is called "pub-in-priv" items). With or without the `pub use`, we set `public =
    /// true`; computing item reachability is harder.
    pub public: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
pub struct FileInfo {}

/// A filename.
#[derive(Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FileName {
    /// A remapped path (namely paths into stdlib)
    Virtual(String),
    /// A local path (a file coming from the current crate for instance)
    Local(String),
    /// A "not real" file name (macro, query, etc.)
    NotReal(String),
}
