//! This file groups everything which is linked to implementations about [crate::meta]
#![allow(dead_code)]

use crate::meta::*;
use rustc_hir::def_id::DefId;
use rustc_index::vec::IndexVec;
use rustc_middle::mir::{SourceInfo, SourceScope, SourceScopeData};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter::Iterator;

/// Retrieve the Rust span from a def id.
///
/// Rem.: we use [TyCtxt::def_span], not [TyCtxt::def_ident_span] to retrieve
/// the span.
pub fn get_rspan_from_def_id(ctx: TyCtxt, def_id: DefId) -> rustc_span::Span {
    ctx.def_span(def_id)
}

impl Loc {
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
}

/// Combine some meta information (useful when we need to compute the
/// meta-information of, say, a sequence).
pub fn combine_meta(m0: &Meta, m1: &Meta) -> Meta {
    // Merge the spans
    assert!(m0.span.file_id == m1.span.file_id);
    let span = Span {
        file_id: m0.span.file_id,
        beg: Loc::min(&m0.span.beg, &m1.span.beg),
        end: Loc::max(&m0.span.end, &m1.span.end),
    };

    // We don't attempt to merge the "generated from" spans: they might
    // come from different files, and even if they come from the same files
    // they might come from different macros, etc.
    Meta {
        span,
        generated_from_span: None,
    }
}

/// Combine all the meta information in a slice.
pub fn combine_meta_iter<'a, T: Iterator<Item = &'a Meta>>(mut ms: T) -> Meta {
    // The iterator should have a next element
    let mut mc: Meta = *ms.next().unwrap();
    for m in ms {
        mc = combine_meta(&mc, m);
    }

    mc
}

pub fn convert_filename(name: &rustc_span::FileName) -> FileName {
    match name {
        rustc_span::FileName::Real(name) => {
            match name {
                rustc_span::RealFileName::LocalPath(path) => FileName::Local(path.clone()),
                rustc_span::RealFileName::Remapped {
                    local_path: _,
                    virtual_name,
                } =>
                // We use the virtual name because it is always available
                {
                    FileName::Virtual(virtual_name.clone())
                }
            }
        }
        rustc_span::FileName::QuoteExpansion(_)
        | rustc_span::FileName::Anon(_)
        | rustc_span::FileName::MacroExpansion(_)
        | rustc_span::FileName::ProcMacroSourceCode(_)
        | rustc_span::FileName::CfgSpec(_)
        | rustc_span::FileName::CliCrateAttr(_)
        | rustc_span::FileName::Custom(_)
        | rustc_span::FileName::DocTest(_, _)
        | rustc_span::FileName::InlineAsm(_) => {
            // We use the debug formatter to generate a filename.
            // This is not ideal, but filenames are for debugging anyway.
            FileName::NotReal(format!("{name:?}"))
        }
    }
}

/// Return the filename from a Rust span.
pub fn get_filename_from_rspan(sess: &Session, span: rustc_span::Span) -> FileName {
    // Retrieve the source map, which contains information about the source file:
    // we need it to be able to interpret the span.
    let source_map = sess.source_map();

    // Retrieve the filename
    let name = source_map.span_to_filename(span);

    // Convert it
    convert_filename(&name)
}

pub fn convert_loc(loc: rustc_span::Loc) -> Loc {
    Loc {
        line: loc.line,
        col: loc.col.0,
    }
}

pub fn translate_span(
    sess: &Session,
    filename_to_id: &HashMap<FileName, FileId::Id>,
    rspan: rustc_span::Span,
) -> Span {
    // Retrieve the source map, which contains information about the source file:
    // we need it to be able to interpret the span.
    let source_map = sess.source_map();

    // Find the source file and the span.
    // It is very annoying: macros get expanded to statements whose spans refer
    // to the file where the macro is defined, not the file where it is used.
    let (beg, end) = source_map.is_valid_span(rspan).unwrap();
    let filename = convert_filename(&beg.file.name);
    let file_id = match &filename {
        FileName::NotReal(_) => {
            // For now we forbid not real filenames
            unimplemented!();
        }
        FileName::Virtual(_) | FileName::Local(_) => {
            let id = filename_to_id.get(&filename);
            assert!(id.is_some(), "File not found: {:?}", filename);
            id.unwrap()
        }
    };

    let beg = convert_loc(beg);
    let end = convert_loc(end);

    // Put together
    Span {
        file_id: *file_id,
        beg,
        end,
    }
}

/// Compute meta data from a Rust span
pub fn get_meta_from_rspan(
    sess: &Session,
    filename_to_id: &HashMap<FileName, FileId::Id>,
    rspan: rustc_span::Span,
) -> Meta {
    // Translate the span
    let span = translate_span(sess, filename_to_id, rspan);

    Meta {
        span,
        generated_from_span: None,
    }
}

/// Compute meta data from a Rust source scope
pub fn get_meta_from_source_info(
    sess: &Session,
    filename_to_id: &HashMap<FileName, FileId::Id>,
    source_scopes: &IndexVec<SourceScope, SourceScopeData<'_>>,
    source_info: SourceInfo,
) -> Meta {
    // Translate the span
    let mut scope_data = source_scopes.get(source_info.scope).unwrap();
    let span = translate_span(sess, filename_to_id, scope_data.span);

    // Lookup the top-most inlined parent scope.
    if scope_data.inlined_parent_scope.is_some() {
        while scope_data.inlined_parent_scope.is_some() {
            let parent_scope = scope_data.inlined_parent_scope.unwrap();
            scope_data = source_scopes.get(parent_scope).unwrap();
        }

        let parent_span = translate_span(sess, filename_to_id, scope_data.span);

        Meta {
            span: parent_span,
            generated_from_span: Some(span),
        }
    } else {
        Meta {
            span,
            generated_from_span: None,
        }
    }
}

/// Compute the meta information for a Rust definition identified by its id.
pub fn get_meta_from_rid(
    sess: &Session,
    tcx: TyCtxt,
    filename_to_id: &HashMap<FileName, FileId::Id>,
    def_id: DefId,
) -> Meta {
    // Retrieve the span from the def id
    let rspan = get_rspan_from_def_id(tcx, def_id);

    get_meta_from_rspan(sess, filename_to_id, rspan)
}

// TODO: remove?
pub fn span_to_string(sess: &Session, span: rustc_span::Span) -> String {
    // Retrieve the source map, which contains information about the source file:
    // we need it to be able to interpret the span.
    let source_map = sess.source_map();

    // Convert the span to lines
    let (beg, end) = source_map.is_valid_span(span).unwrap();

    // Retrieve the sources snippet:
    let snippet = source_map.span_to_snippet(span);

    // First convert the filename to a string.
    // The file is not necessarily a "real" file, because the span might come
    // from various locations: expanded macro, command line, custom sources, etc.
    // For our purposes, we should only have to deal with real filenames (so
    // we ignore the others).
    match &beg.file.name {
        rustc_span::FileName::Real(filename) => {
            let mut out;

            // Even if the file is real, it may be a remapped path (for
            // example if it is a path into libstd), in which case we use the
            // local path, which points to the proper file on the user's file
            // system.
            match &filename {
                rustc_span::RealFileName::LocalPath(path) => {
                    out = path.as_path().to_str().unwrap().to_string();
                }
                rustc_span::RealFileName::Remapped {
                    local_path,
                    virtual_name: _,
                } => {
                    out = local_path.as_deref().unwrap().to_str().unwrap().to_string();
                }
            }

            // Add the lines to the string.
            out.push_str(&format!(
                ", start: line {} column {}, end: line {} column {}",
                beg.line, beg.col.0, end.line, end.col.0
            ));

            // Add the code snippet
            let _ = snippet.map(|snippet| out.push_str(&format!("\nCode snippet:\n{snippet}")));
            out
        }
        // Other cases: just return a dummy string
        _ => "<unknown span>".to_string(),
    }
}
