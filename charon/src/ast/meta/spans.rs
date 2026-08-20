use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};
use std::{borrow::Cow, cmp::Ordering, ops::Range, path::PathBuf};

generate_index_type!(FileId);

/// A filename.
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    DriveTwo,
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

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct File {
    /// The file identifier.
    #[cfg_attr(feature = "charon_on_charon", charon::opaque)]
    pub id: FileId,
    /// The path to the file.
    #[drive(skip)]
    pub name: FileName,
    /// Name of the crate this file comes from.
    pub crate_name: String,
    /// The contents of the source file, as seen by rustc at the time of translation.
    /// Some files don't have contents.
    pub contents: Option<String>,
}

#[derive(
    Debug,
    Copy,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[drive(skip)]
pub struct Loc {
    /// The (1-based) line number.
    pub line: usize,
    /// The (0-based) column offset.
    pub col: usize,
}

/// A snippet of source code within a file.
#[derive(
    Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut, DriveTwo,
)]
pub struct SpanData {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("file"))]
    pub file_id: FileId,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("beg_loc"))]
    pub beg: Loc,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("end_loc"))]
    pub end: Loc,
}

/// A snippet of source code within a file.
#[derive(
    Debug,
    Copy,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[serde_state(stateless)]
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
    ///     macro!(); // <-- `data` refers to this location
    /// }
    /// ```
    pub data: SpanData,
    /// Where the code actually comes from, in case of macro expansion/inlining/etc.
    pub generated_from_span: Option<SpanData>,
}

/// Given a line number within a source file, get the byte of the start of the line. Obviously not
/// efficient to do many times, but this is used is diagnostic paths only. The line numer is
/// expected to be 1-based.
fn line_to_start_byte(source: &str, line_nbr: usize) -> usize {
    let mut cur_byte = 0;
    for (i, line) in source.split_inclusive('\n').enumerate() {
        if line_nbr == i + 1 {
            break;
        }
        cur_byte += line.len();
    }
    cur_byte
}

impl Loc {
    fn dummy() -> Self {
        Loc { line: 0, col: 0 }
    }

    fn min(l0: &Loc, l1: &Loc) -> Loc {
        match l0.line.cmp(&l1.line) {
            Ordering::Equal => Loc {
                line: l0.line,
                col: std::cmp::min(l0.col, l1.col),
            },
            Ordering::Less => *l0,
            Ordering::Greater => *l1,
        }
    }

    fn max(l0: &Loc, l1: &Loc) -> Loc {
        match l0.line.cmp(&l1.line) {
            Ordering::Equal => Loc {
                line: l0.line,
                col: std::cmp::max(l0.col, l1.col),
            },
            Ordering::Greater => *l0,
            Ordering::Less => *l1,
        }
    }

    pub fn to_byte(self, source: &str) -> usize {
        line_to_start_byte(source, self.line) + self.col
    }
}

impl SpanData {
    pub fn dummy() -> Self {
        SpanData {
            file_id: FileId::from_raw(0),
            beg: Loc::dummy(),
            end: Loc::dummy(),
        }
    }

    /// Value with which we order `SpanDatas`s.
    fn sort_key(&self) -> impl Ord {
        (self.file_id, self.beg, self.end)
    }

    pub fn to_byte_range(self, source: &str) -> Range<usize> {
        self.beg.to_byte(source)..self.end.to_byte(source)
    }
}

/// Manual impls because `SpanData` is not orderable.
impl PartialOrd for SpanData {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SpanData {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
}

impl Span {
    pub fn dummy() -> Self {
        Span {
            data: SpanData::dummy(),
            generated_from_span: None,
        }
    }
}

/// Combine some span information (useful when we need to compute the
/// span-information of, say, a sequence).
pub fn combine_span(m0: &Span, m1: &Span) -> Span {
    // Merge the spans
    if m0.data.file_id == m1.data.file_id {
        let data = SpanData {
            file_id: m0.data.file_id,
            beg: Loc::min(&m0.data.beg, &m1.data.beg),
            end: Loc::max(&m0.data.end, &m1.data.end),
        };

        // We don't attempt to merge the "generated from" spans: they might
        // come from different files, and even if they come from the same files
        // they might come from different macros, etc.
        Span {
            data,
            generated_from_span: None,
        }
    } else {
        // It happens that the spans don't come from the same file. In this
        // situation, we just return the first span. TODO: improve this.
        *m0
    }
}

/// Combine all the span information in a slice.
pub fn combine_span_iter<'a, T: Iterator<Item = &'a Span>>(mut ms: T) -> Span {
    // The iterator should have a next element
    let mut mc: Span = ms.next().copied().unwrap_or_default();
    for m in ms {
        mc = combine_span(&mc, m);
    }

    mc
}

impl FileName {
    pub fn to_string(&self) -> Cow<'_, str> {
        match self {
            FileName::Virtual(path_buf) | FileName::Local(path_buf) => path_buf.to_string_lossy(),
            FileName::NotReal(path) => Cow::Borrowed(path),
        }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::dummy()
    }
}
