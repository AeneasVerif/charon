//! Meta-information about programs (spans, etc.).

pub use crate::meta_utils::*;
use macros::{EnumAsGetters, EnumIsA};
use serde::Serialize;

generate_index_type!(LocalFileId);
generate_index_type!(VirtualFileId);

#[allow(non_snake_case)]
pub mod FileId {
    use crate::meta::*;

    #[derive(
        Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, EnumIsA, EnumAsGetters, Serialize,
    )]
    pub enum Id {
        LocalId(LocalFileId::Id),
        VirtualId(VirtualFileId::Id),
    }
}

#[derive(Debug, Copy, Clone, Serialize)]
pub struct Loc {
    /// The (1-based) line number.
    pub line: usize,
    /// The (0-based) column offset.
    pub col: usize,
}

/// Span information
#[derive(Debug, Copy, Clone, Serialize)]
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
    pub rust_span_data: rustc_span::SpanData,
}

/// Meta information about a piece of code (block, statement, etc.)
#[derive(Debug, Copy, Clone, Serialize)]
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

/// Attributes (`#[...]`). For now we store just the string representation.
pub type Attribute = String;

/// `#[inline]` built-in attribute.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize)]
pub enum InlineAttr {
    /// `#[inline]`
    Hint,
    /// `#[inline(never)]`
    Never,
    /// `#[inline(always)]`
    Always,
}

/// Meta information about an item (function, trait decl, trait impl, type decl, global).
#[derive(Debug, Clone, Serialize)]
pub struct ItemMeta {
    pub meta: Meta,
    /// Attributes (`#[...]`).
    pub attributes: Vec<Attribute>,
    /// Inline hints (on functions only).
    pub inline: Option<InlineAttr>,
    /// Whether this item is public. Note that this considers pub-in-priv items to be public.
    /// Computing actual reachability is harder.
    pub public: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize)]
pub struct FileInfo {}

/// A filename.
#[derive(Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Serialize)]
pub enum FileName {
    /// A remapped path (namely paths into stdlib)
    Virtual(String),
    /// A local path (a file coming from the current crate for instance)
    Local(String),
    /// A "not real" file name (macro, query, etc.)
    NotReal(String),
}
