//! Meta-information about programs (spans, etc.).

pub use crate::meta_utils::*;
use crate::names::Name;
use derive_visitor::{Drive, DriveMut};
use hax_frontend_exporter::PathBuf;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters};
use serde::{Deserialize, Serialize};

generate_index_type!(LocalFileId);
generate_index_type!(VirtualFileId);

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
    Drive,
    DriveMut,
)]
pub enum FileId {
    LocalId(LocalFileId),
    VirtualId(VirtualFileId),
}

#[derive(Debug, Copy, Clone, Serialize, Deserialize, Drive, DriveMut)]
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
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct RawSpan {
    pub file_id: FileId,
    pub beg: Loc,
    pub end: Loc,
    /// We keep the rust span so as to be able to leverage Rustc to print
    /// error messages (useful in the micro-passes for instance).
    /// We use `Span` instead of `SpanData` because `Span` is not `Send` when rustc runs
    /// single-threaded (default on older versions). We need this to be `Send` because we pass this
    /// data out of the rustc callbacks in charon-driver.
    #[serde(skip)]
    #[drive(skip)]
    #[serde(default = "dummy_span_data")]
    pub rust_span_data: rustc_span::SpanData,
}

impl From<RawSpan> for rustc_error_messages::MultiSpan {
    fn from(span: RawSpan) -> Self {
        span.rust_span_data.span().into()
    }
}

/// Meta information about a piece of code (block, statement, etc.)
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct Span {
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
    pub span: RawSpan,
    /// Where the code actually comes from, in case of macro expansion/inlining/etc.
    pub generated_from_span: Option<RawSpan>,
}

impl From<Span> for rustc_error_messages::MultiSpan {
    fn from(span: Span) -> Self {
        span.span.into()
    }
}

/// `#[inline]` built-in attribute.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub enum InlineAttr {
    /// `#[inline]`
    Hint,
    /// `#[inline(never)]`
    Never,
    /// `#[inline(always)]`
    Always,
}

/// Attributes (`#[...]`).
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
pub enum Attribute {
    Opaque,
    Rename(String),
    Unknown(String),
}

/// Information about the attributes and visibility of an item, field or variant..
#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct AttrInfo {
    /// Attributes (`#[...]`).
    pub attributes: Vec<Attribute>,
    /// Inline hints (on functions only).
    pub inline: Option<InlineAttr>,
    /// Attribute `charon::rename("...")` provide a custom name that can be used by consumers of
    /// llbc. E.g. Aeneas uses this to rename definitions in the extracted code.
    pub rename: Option<String>,
    /// Whether there was a `#[charon::opaque]` annotation on this item. This is different from
    /// other reasons this may be opaque.
    #[serde(skip_serializing)]
    #[serde(default)]
    pub opaque: bool,
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

/// Meta information about an item (function, trait decl, trait impl, type decl, global).
#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct ItemMeta {
    pub span: Span,
    pub name: Name,
    /// Attributes and visibility.
    pub attr_info: AttrInfo,
    /// `true` if the type decl is a local type decl, `false` if it comes from an external crate.
    pub is_local: bool,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize, Drive, DriveMut)]
pub struct FileInfo {}

/// A filename.
#[derive(
    Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Serialize, Deserialize, Drive, DriveMut,
)]
pub enum FileName {
    /// A remapped path (namely paths into stdlib)
    #[drive(skip)] // drive is not implemented for `PathBuf`
    Virtual(PathBuf),
    /// A local path (a file coming from the current crate for instance)
    #[drive(skip)] // drive is not implemented for `PathBuf`
    Local(PathBuf),
    /// A "not real" file name (macro, query, etc.)
    NotReal(String),
}
