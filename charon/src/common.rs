#![allow(dead_code)]

use im::Vector;
use rustc_errors::DiagnosticId;
use rustc_session::Session;
use rustc_span::MultiSpan;
use serde::{Serialize, Serializer};

/// Our redefinition of Result - we don't care much about the I/O part.
pub type Result<T> = std::result::Result<T, ()>;

/// We use both `ErrorEmitter` and the logger to report errors and warnings.
/// Those two ways of reporting information don't target the same usage and
/// the same users.
/// - `ErrorEmitter` allows us to report a limited number clean messages to
///   the user, with the same formatting as the compiler messages.
/// - On the other hand, the logger allows us to report and filter a big number
///   of detailed messages, for debugging purposes.
pub trait ErrorEmitter {
    fn span_err<S: Into<MultiSpan>>(&self, s: S, msg: &str);

    fn span_warn<S: Into<MultiSpan>>(&self, s: S, msg: &str);
}

impl ErrorEmitter for Session {
    fn span_err<S: Into<MultiSpan>>(&self, s: S, msg: &str) {
        self.span_err_with_code(s, msg, DiagnosticId::Error(String::from("Aenea")));
    }

    fn span_warn<S: Into<MultiSpan>>(&self, s: S, msg: &str) {
        self.span_warn_with_code(s, msg, DiagnosticId::Error(String::from("Aenea")));
    }
}

pub fn span_err(sess: &Session, span: rustc_span::Span, msg: &str) {
    log::error!("{}:\n{}", span_to_string(sess, span), msg);
    sess.span_err(span, msg);
}

pub fn span_warn(sess: &Session, span: rustc_span::Span, msg: &str) {
    log::warn!("{}:\n{}", span_to_string(sess, span), msg);
    sess.span_warn(span, msg);
}

pub fn span_to_string(sess: &Session, span: rustc_span::Span) -> String {
    // Retrieve the source map, which contains information about the source file:
    // we need it to be able to interpret the span.
    let source_map = sess.source_map();

    // Convert the span to lines (i.e.: a filename and a list of lines in
    // this file).
    let lines = source_map.span_to_lines(span).unwrap();

    // Retrieve the sources snippet:
    let snippet = source_map.span_to_snippet(span);

    // First convert the filename to a string.
    // The file is not necessarily a "real" file, because the span might come
    // from various locations: expanded macro, command line, custom sources, etc.
    // For our purposes, we should only have to deal with real filenames (so
    // we ignore the others).
    match &lines.file.name {
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
            // Note that the vector of lines lists all the lines over which
            // the span expands. We make the hypothesis that it is a continuous
            // set of lines, and thus only indicate the
            let len = lines.lines.len();
            if len > 0 {
                let beg = &lines.lines[0];
                let end = &lines.lines[len - 1];
                out.push_str(&format!(
                    ", start: line {} column {}, end: line {} column {}",
                    beg.line_index, beg.start_col.0, end.line_index, end.end_col.0
                ));
            }

            // Add the code snippet
            let _ = snippet.map(|snippet| out.push_str(&format!("\nCode snippet:\n{}", snippet)));
            return out;
        }
        // Other cases: just return a dummy string
        _ => {
            return "<unknown span>".to_string();
        }
    }
}

/// Custom function to pretty-print elements from an iterator
/// The output format is:
/// ```
/// [
///   elem_0,
///   ...
///   elem_n
/// ]
/// ```
pub fn iterator_to_string<T>(
    t_to_string: &dyn Fn(T) -> String,
    it: impl Iterator<Item = T>,
) -> String {
    let elems: Vec<String> = it
        .map(|x| format!("  {}", t_to_string(x)).to_owned())
        .collect();
    if elems.len() == 0 {
        "[]".to_owned()
    } else {
        format!("[\n{}\n]", elems.join(",\n")).to_owned()
    }
}

/// Custom function to pretty-print a vector.
pub fn vector_to_string<T>(t_to_string: &dyn Fn(&T) -> String, v: &Vec<T>) -> String {
    iterator_to_string(t_to_string, v.iter())
}

/// Assertion which doesn't panick
pub fn assert(x: bool) -> Result<()> {
    if x {
        Ok(())
    } else {
        Err(())
    }
}

/// This macro computes the name of the function in which it is called.
/// We adapted it from:
/// https://stackoverflow.com/questions/38088067/equivalent-of-func-or-function-in-rust
/// Note that we can't define it in aenea_macros due to technical reasons
macro_rules! function_name {
    () => {{
        fn f() {}
        fn type_name_of<T>(_: T) -> &'static str {
            std::any::type_name::<T>()
        }
        let name = type_name_of(f);

        // Remove the "::f" suffix
        let name = &name[..name.len() - 3];

        // Remove the CRATE::MODULE:: prefix
        let name = match &name.find("::") {
            Some(pos) => &name[pos + 2..name.len()],
            None => name,
        };

        match &name.find("::") {
            Some(pos) => &name[pos + 2..name.len()],
            None => name,
        }
    }};
}

/// A custom log trace macro. Uses the log crate.
macro_rules! trace {
    ($($arg:tt)+) => {{
        let msg = format!($($arg)+);
        log::trace!("[{}]:\n{}", function_name!(), msg)
    }};
    () => {{
        log::trace!("[{}]", function_name!())
    }};
}

/// A custom log error macro. Uses the log crate.
macro_rules! error {
    ($($arg:tt)+) => {{
        let msg = format!($($arg)+);
        log::error!("[{}]:\n{}", function_name!(), msg)
    }};
}

pub fn serialize_vector<T: Clone + Serialize, S: Serializer>(
    v: &Vector<T>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error> {
    use serde::ser::SerializeSeq;
    let mut seq = serializer.serialize_seq(Some(v.len()))?;
    for e in v {
        seq.serialize_element(e)?;
    }
    seq.end()
}

/// Wrapper to serialize vectors from im::Vector.
///
/// We need this because serialization is implemented via the trait system.
pub struct VectorSerializer<'a, T: Clone> {
    pub vector: &'a Vector<T>,
}

impl<'a, T: Clone> VectorSerializer<'a, T> {
    pub fn new(vector: &'a Vector<T>) -> Self {
        VectorSerializer { vector }
    }
}

impl<'a, T: Clone + Serialize> Serialize for VectorSerializer<'a, T> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_vector(&self.vector, serializer)
    }
}
