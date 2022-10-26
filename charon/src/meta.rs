//! Meta-information about programs (spans, etc.).

pub use crate::meta_utils::*;
use macros::{generate_index_type, EnumAsGetters, EnumIsA};
use serde::Serialize;
use std::path::PathBuf;

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

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize)]
pub struct FileInfo {}

/// A filename.
#[derive(Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Serialize)]
pub enum FileName {
    /// A remapped path (namely paths into stdlib)
    Virtual(PathBuf),
    /// A local path (a file coming from the current crate for instance)
    Local(PathBuf),
    /// A "not real" file name (macro, query, etc.)
    NotReal(String),
}
