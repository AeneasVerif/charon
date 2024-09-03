extern crate env_logger;

/// Initialize the logger.
pub fn initialize_logger() {
    {
        // Initialize the logger only once (useful when running the driver in tests).
        use std::sync::atomic::{AtomicBool, Ordering};
        static LOGGER_INITIALIZED: AtomicBool = AtomicBool::new(false);
        if LOGGER_INITIALIZED.swap(true, Ordering::SeqCst) {
            return;
        }
    }

    use tracing_subscriber::prelude::*;
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(
            tracing_tree::HierarchicalLayer::new(1)
                .with_ansi(true)
                .with_indent_lines(true)
                .with_bracketed_fields(true)
                .with_timer(tracing_tree::time::Uptime::default()),
        )
        .init();
}

/// This macro computes the name of the function in which it is called and the line number.
/// We adapted it from:
/// <https://stackoverflow.com/questions/38088067/equivalent-of-func-or-function-in-rust>
#[macro_export]
macro_rules! code_location {
    ($color:ident) => {{
        fn f() {}
        fn type_name_of<T>(_: T) -> &'static str {
            std::any::type_name::<T>()
        }
        let name = type_name_of(f);

        let path: Vec<_> = name.split("::").collect();
        // The path looks like `crate::module::function::f`.
        let name = path.iter().rev().skip(1).next().unwrap();

        let line = line!();
        let file = file!();

        use colored::Colorize;
        let name = name.$color();
        let location = format!("{file}:{line}").dimmed();
        format!("in {name} at {location}")
    }};
}

/// A custom log trace macro. Uses the log crate.
#[macro_export]
macro_rules! trace {
    ($($arg:tt)+) => {{
        let msg = format!($($arg)+);
        tracing::trace!("{}:\n{}", $crate::code_location!(yellow), msg)
    }};
    () => {{
        tracing::trace!("{}", $crate::code_location!(yellow))
    }};
}

/// A custom log error macro. Uses the log crate.
#[macro_export]
macro_rules! error {
    ($($arg:tt)+) => {{
        let msg = format!($($arg)+);
        tracing::error!("{}:\n{}", $crate::code_location!(red), msg)
    }};
}

/// A custom log warn macro. Uses the log crate.
#[macro_export]
macro_rules! warn {
    ($($arg:tt)+) => {{
        let msg = format!($($arg)+);
        tracing::warn!("{}:\n{}", $crate::code_location!(yellow), msg)
    }};
}

/// A custom log info macro. Uses the log crate.
#[macro_export]
macro_rules! info {
    ($($arg:tt)+) => {{
        let msg = format!($($arg)+);
        // As for info we generally output simple messages, we don't insert
        // a breakline
        tracing::info!("{}: {}", $crate::code_location!(yellow), msg)
    }};
    () => {{
        tracing::info!("{}", $crate::code_location!(yellow))
    }};
}
