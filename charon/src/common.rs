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
