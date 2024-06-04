pub static TAB_INCR: &str = "    ";

/// Common error used during the translation.
#[derive(Debug)]
pub struct Error {
    pub span: rustc_span::Span,
    pub msg: String,
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

// This is the amount of bytes that need to be left on the stack before increasing the size. It
// must be at least as large as the stack required by any code that does not call
// `ensure_sufficient_stack`.
const RED_ZONE: usize = 100 * 1024; // 100k

// Only the first stack that is pushed, grows exponentially (2^n * STACK_PER_RECURSION) from then
// on. Values taken from rustc.
const STACK_PER_RECURSION: usize = 1024 * 1024; // 1MB

/// Grows the stack on demand to prevent stack overflow. Call this in strategic locations to "break
/// up" recursive calls. E.g. most statement visitors can benefit from this.
#[inline]
pub fn ensure_sufficient_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(RED_ZONE, STACK_PER_RECURSION, f)
}
