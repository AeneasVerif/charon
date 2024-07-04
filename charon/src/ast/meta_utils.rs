//! This file groups everything which is linked to implementations about [crate::meta]
use crate::meta::*;
use crate::names::{Disambiguator, Name, PathElem};
use hax_frontend_exporter as hax;
use rustc_ast::{AttrArgs, NormalAttr};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use std::cmp::Ordering;
use std::iter::Iterator;
use std::path::Component;

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

/// Combine some span information (useful when we need to compute the
/// span-information of, say, a sequence).
pub fn combine_span(m0: &Span, m1: &Span) -> Span {
    // Merge the spans
    if m0.span.file_id == m1.span.file_id {
        let span = RawSpan {
            file_id: m0.span.file_id,
            beg: Loc::min(&m0.span.beg, &m1.span.beg),
            end: Loc::max(&m0.span.end, &m1.span.end),
            rust_span_data: m0
                .span
                .rust_span_data
                .span()
                .to(m1.span.rust_span_data.span())
                .data(),
        };

        // We don't attempt to merge the "generated from" spans: they might
        // come from different files, and even if they come from the same files
        // they might come from different macros, etc.
        Span {
            span,
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
    let mut mc: Span = *ms.next().unwrap();
    for m in ms {
        mc = combine_span(&mc, m);
    }

    mc
}

pub fn convert_filename(name: &hax::FileName) -> FileName {
    match name {
        hax::FileName::Real(name) => {
            use hax::RealFileName;
            match name {
                RealFileName::LocalPath(path) => FileName::Local(path.clone()),
                RealFileName::Remapped { virtual_name, .. } => {
                    // We use the virtual name because it is always available.
                    // That name normally starts with `/rustc/<hash>/`. For our purposes we hide
                    // the hash.
                    let mut components_iter = virtual_name.components();
                    if let Some(
                        [Component::RootDir, Component::Normal(rustc), Component::Normal(hash)],
                    ) = components_iter.by_ref().array_chunks().next()
                        && rustc.to_str() == Some("rustc")
                        && hash.len() == 40
                    {
                        let path_without_hash = [Component::RootDir, Component::Normal(rustc)]
                            .into_iter()
                            .chain(components_iter)
                            .collect();
                        FileName::Virtual(path_without_hash)
                    } else {
                        FileName::Virtual(virtual_name.clone())
                    }
                }
            }
        }
        hax::FileName::QuoteExpansion(_)
        | hax::FileName::Anon(_)
        | hax::FileName::MacroExpansion(_)
        | hax::FileName::ProcMacroSourceCode(_)
        | hax::FileName::CliCrateAttr(_)
        | hax::FileName::Custom(_)
        | hax::FileName::DocTest(..)
        | hax::FileName::InlineAsm(_) => {
            // We use the debug formatter to generate a filename.
            // This is not ideal, but filenames are for debugging anyway.
            FileName::NotReal(format!("{name:?}"))
        }
    }
}

pub fn convert_loc(loc: hax::Loc) -> Loc {
    Loc {
        line: loc.line,
        col: loc.col,
    }
}

// TODO: remove?
pub fn span_to_string(source_map: &SourceMap, span: rustc_span::Span) -> String {
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

impl Attribute {
    pub(crate) fn parse(normal_attr: &NormalAttr, span: rustc_span::Span) -> Result<Self, String> {
        // We use `pprust` to render the attribute somewhat like it is written in the source.
        // WARNING: this can change whitespace, and sometimes even adds newlines. Maybe we
        // should use spans and SourceMap info instead.
        use rustc_ast_pretty::pprust::PrintState;

        // If the attribute path has two components, the first of which is `charon` or `aeneas`, we
        // try to parse it. Otherwise we return `Unknown`.
        let attr_name = if let [path_start, attr_name] = normal_attr.item.path.segments.as_slice()
            && let path_start = path_start.ident.as_str()
            && (path_start == "charon" || path_start == "aeneas")
        {
            attr_name.ident.as_str()
        } else {
            let full_attr = rustc_ast_pretty::pprust::State::to_string(|s| {
                s.print_attr_item(&normal_attr.item, span)
            });
            return Ok(Self::Unknown(full_attr));
        };

        let args = match &normal_attr.item.args {
            AttrArgs::Empty => None,
            AttrArgs::Delimited(args) => Some(rustc_ast_pretty::pprust::State::to_string(|s| {
                s.print_tts(&args.tokens, false)
            })),
            AttrArgs::Eq(..) => unimplemented!("`#[charon::foo = val]` syntax is unsupported"),
        };
        match attr_name {
            // `#[charon::opaque]`
            "opaque" if args.is_none() => Ok(Self::Opaque),
            // `#[charon::rename("new_name")]`
            "rename" if let Some(attr) = args => {
                let Some(attr) = attr
                    .strip_prefix("\"")
                    .and_then(|attr| attr.strip_suffix("\""))
                else {
                    return Err(format!(
                        "the new name should be between quotes: `rename(\"{attr}\")`."
                    ));
                };

                if attr.is_empty() {
                    return Err(format!("attribute `rename` should not be empty"));
                }

                let first_char = attr.chars().nth(0).unwrap();
                let is_identifier = (first_char.is_alphabetic() || first_char == '_')
                    && attr.chars().all(|c| c.is_alphanumeric() || c == '_');
                if !is_identifier {
                    return Err(format!(
                        "attribute `rename` should contain a valid identifier"
                    ));
                }

                Ok(Self::Rename(attr.to_string()))
            }
            // `#[charon::variants_prefix("T")]`
            "variants_prefix" if let Some(attr) = args => {
                let Some(attr) = attr
                    .strip_prefix("\"")
                    .and_then(|attr| attr.strip_suffix("\""))
                else {
                    return Err(format!(
                        "the name should be between quotes: `variants_prefix(\"{attr}\")`."
                    ));
                };

                Ok(Self::VariantsPrefix(attr.to_string()))
            }
            // `#[charon::variants_suffix("T")]`
            "variants_suffix" if let Some(attr) = args => {
                let Some(attr) = attr
                    .strip_prefix("\"")
                    .and_then(|attr| attr.strip_suffix("\""))
                else {
                    return Err(format!(
                        "the name should be between quotes: `variants_suffix(\"{attr}\")`."
                    ));
                };

                Ok(Self::VariantsSuffix(attr.to_string()))
            }
            _ => {
                let full_attr = rustc_ast_pretty::pprust::State::to_string(|s| {
                    s.print_attr_item(&normal_attr.item, span)
                });
                Err(format!("Unrecognized attribute: `{full_attr}`"))
            }
        }
    }
}

impl ItemOpacity {
    pub(crate) fn with_content_visibility(self, contents_are_public: bool) -> Self {
        use ItemOpacity::*;
        match self {
            Transparent => Transparent,
            Foreign if contents_are_public => Transparent,
            Foreign => Opaque,
            Opaque => Opaque,
        }
    }

    pub(crate) fn with_private_contents(self) -> Self {
        self.with_content_visibility(false)
    }
}

impl ItemMeta {
    pub fn renamed_name(&self) -> Name {
        let mut name = self.name.clone();
        if let Some(rename) = self.attr_info.rename.clone() {
            *name.name.last_mut().unwrap() = PathElem::Ident(rename, Disambiguator::new(0));
        }
        name
    }
}
