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
