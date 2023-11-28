#![allow(dead_code)]

use crate::meta;
use im::Vector;
use rustc_error_messages::MultiSpan;
use rustc_errors::DiagnosticId;
use rustc_session::Session;
use serde::{Serialize, Serializer};
use std::iter::FromIterator;

pub static TAB_INCR: &str = "    ";

/// Propagate the error from a callback to the caller :
/// Used to avoid saving, checking and returning the result by hand.
/// The callback will not be called again if it returned an error.
/// The dynamic signature is used to pass a generic function as argument.
/// A simple use case is shown in `test_propagate_error`.
pub fn propagate_error<T, C, F>(consumer: C, mut callback: F) -> Result<(), ()>
where
    F: FnMut(T) -> Result<(),()>,
    C: FnOnce(&mut dyn FnMut(T)),
{
    let mut res = Ok(());
    consumer(&mut |arg: T| {
        if res.is_ok() {
            res = callback(arg);
        }
    });
    res
}

/// We use both `ErrorEmitter` and the logger to report errors and warnings.
/// Those two ways of reporting information don't target the same usage and
/// the same users.
/// - `ErrorEmitter` allows us to report a limited number of messages to
///   the user, with the same formatting as the compiler messages.
/// - On the other hand, the logger allows us to report and filter a big number
///   of detailed messages, for debugging purposes.
pub trait ErrorEmitter {
    fn span_err<S: Into<MultiSpan>>(&self, s: S, msg: &'static str);

    fn span_warn<S: Into<MultiSpan>>(&self, s: S, msg: &'static str);
}

impl ErrorEmitter for Session {
    fn span_err<S: Into<MultiSpan>>(&self, s: S, msg: &'static str) {
        self.span_err_with_code(s, msg, DiagnosticId::Error(String::from("Aeneas")));
    }

    fn span_warn<S: Into<MultiSpan>>(&self, s: S, msg: &'static str) {
        self.span_warn_with_code(s, msg, DiagnosticId::Error(String::from("Aeneas")));
    }
}

pub fn span_err(sess: &Session, span: rustc_span::Span, msg: &'static str) {
    log::error!("{}:\n{}", meta::span_to_string(sess, span), msg);
    sess.span_err(span, msg);
}

pub fn span_warn(sess: &Session, span: rustc_span::Span, msg: &'static str) {
    log::warn!("{}:\n{}", meta::span_to_string(sess, span), msg);
    sess.span_warn(span, msg);
}

/// Custom function to pretty-print elements from an iterator
/// The output format is:
/// ```text
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
    let elems: Vec<String> = it.map(|x| format!("  {}", t_to_string(x))).collect();
    if elems.is_empty() {
        "[]".to_owned()
    } else {
        format!("[\n{}\n]", elems.join(",\n"))
    }
}

/// Custom function to pretty-print a vector.
pub fn vec_to_string<T>(t_to_string: &dyn Fn(&T) -> String, v: &[T]) -> String {
    iterator_to_string(t_to_string, v.iter())
}

/// Rk.: in practice, T should be a shared ref
pub fn write_iterator<T: Copy>(
    write_t: &dyn Fn(&mut std::fmt::Formatter<'_>, T) -> std::result::Result<(), std::fmt::Error>,
    f: &mut std::fmt::Formatter<'_>,
    it: impl Iterator<Item = T>,
) -> std::result::Result<(), std::fmt::Error> {
    let elems: Vec<T> = it.collect();
    if elems.is_empty() {
        write!(f, "[]")
    } else {
        writeln!(f, "[")?;
        for i in 0..elems.len() {
            write_t(f, elems[i])?;
            if i + 1 < elems.len() {
                writeln!(f, ",")?;
            }
        }
        write!(f, "\n]")
    }
}

pub fn write_vec<T>(
    write_t: &dyn Fn(&mut std::fmt::Formatter<'_>, &T) -> std::result::Result<(), std::fmt::Error>,
    f: &mut std::fmt::Formatter<'_>,
    v: &[T],
) -> std::result::Result<(), std::fmt::Error> {
    write_iterator(write_t, f, v.iter())
}

/// Assertion which doesn't panick
pub fn assert(x: bool) -> Result<(),()> {
    if x {
        Ok(())
    } else {
        Err(())
    }
}

/// This macro computes the name of the function in which it is called.
/// We adapted it from:
/// <https://stackoverflow.com/questions/38088067/equivalent-of-func-or-function-in-rust>
/// Note that we can't define it in macros due to technical reasons
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
        use colored::Colorize;
        let msg = format!($($arg)+);
        log::trace!("[{}]:\n{}", function_name!().yellow(), msg)
    }};
    () => {{
        use colored::Colorize;
        log::trace!("[{}]", function_name!().yellow())
    }};
}

/// A custom log error macro. Uses the log crate.
macro_rules! error {
    ($($arg:tt)+) => {{
        use colored::Colorize;
        let msg = format!($($arg)+);
        log::error!("[{}]:\n{}", function_name!().red(), msg)
    }};
}

/// A custom log info macro. Uses the log crate.
macro_rules! info {
    ($($arg:tt)+) => {{
        use colored::Colorize;
        let msg = format!($($arg)+);
        // As for info we generally output simple messages, we don't insert
        // a breakline
        log::info!("[{}]: {}", function_name!().yellow(), msg)
    }};
    () => {{
        log::info!("[{}]", function_name!().yellow())
    }};
}

/// Serialize a vector
pub fn serialize_vec<T: Serialize, S: Serializer>(
    v: &Vec<T>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error> {
    use serde::ser::SerializeSeq;
    // Note that we don't write the sequence length in the json file: it causes
    // errors with OCaml's Yojson (because then we mix named fields with unnamed
    // fields).
    let mut seq = serializer.serialize_seq(Some(v.len()))?;
    for e in v {
        seq.serialize_element(e)?;
    }
    seq.end()
}

/// Serialize a collection by using an iterator on this collection
pub fn serialize_collection<T: Serialize, I: IntoIterator<Item = T>, S: Serializer>(
    it: I,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error> {
    // For simplicity, we convert to a vec (this gives us the length)
    let v = Vec::from_iter(it);
    serialize_vec(&v, serializer)
}

pub fn serialize_vector<T: Clone + Serialize, S: Serializer>(
    v: &Vector<T>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error> {
    serialize_collection(v.iter(), serializer)
}

/// Wrapper to serialize std::vec::Vec
///
/// We need this because serialization is implemented via the trait system.
pub struct VecSerializer<'a, T> {
    pub vector: &'a Vec<T>,
}

impl<'a, T> VecSerializer<'a, T> {
    pub fn new(vector: &'a Vec<T>) -> Self {
        VecSerializer { vector }
    }
}

impl<'a, T: Serialize> Serialize for VecSerializer<'a, T> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_vec(self.vector, serializer)
    }
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
        serialize_vector(self.vector, serializer)
    }
}

#[test]
fn test_propagate_error() {
    let ints = &[1, 2, 3, 4, 5, 6];
    let mut sum = 0;
    let res = propagate_error(
        |f| ints.iter().for_each(f),
        |x| {
            if *x == 4 {
                return Err(());
            }
            sum += *x;
            Ok(())
        },
    );
    assert!(res.is_err());
    assert!(sum == 6);
}
