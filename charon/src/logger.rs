extern crate env_logger;

/// Initialize the logger. We use a custom initialization to add some
/// useful debugging information, including the line number in the file.
pub fn initialize_logger() {
    {
        // Initialize the logger only once (useful when running the driver in tests).
        use std::sync::atomic::{AtomicBool, Ordering};
        static LOGGER_INITIALIZED: AtomicBool = AtomicBool::new(false);
        if LOGGER_INITIALIZED.swap(true, Ordering::SeqCst) {
            return;
        }
    }
    use env_logger::fmt::style;
    use env_logger::{Builder, Env};
    use std::io::Write;

    // Create a default environment, by using the environment variables.
    // We do this to let the user choose the log level (i.e.: trace,
    // debug, warning, etc.)
    let env = Env::default();
    // If the log level is not set, set it to "info"
    let env = env.default_filter_or("info");

    // Initialize the log builder from the environment we just created
    let mut builder = Builder::from_env(env);

    // Modify the output format - we add the line number
    builder.format(|buf, record| {
        // Retreive the path (CRATE::MODULE) and the line number
        let path = record.module_path().unwrap_or_default();
        let line = record.line().unwrap_or_default();

        // Style for the brackets (change the color)
        let brackets_style = style::RgbColor(120, 120, 120).on_default();
        let level_style = buf.default_level_style(record.level()); // Print the level with colors

        write!(buf, "{brackets_style}[{brackets_style:#}")?;
        write!(
            buf,
            "{level_style}{}{level_style:#} {path}:{line}",
            record.level(),
        )?;
        write!(buf, "{brackets_style}]{brackets_style:#} ")?;
        writeln!(buf, "{}", record.args())?;
        Ok(())
    });

    builder.init();

    // Also set up `tracing` so we get tracing data from `hax`.
    use tracing_subscriber::prelude::*;
    let subscriber = tracing_subscriber::Registry::default()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(
            tracing_tree::HierarchicalLayer::new(2)
                .with_ansi(true)
                .with_indent_amount(1)
                .with_indent_lines(true),
        );
    tracing::subscriber::set_global_default(subscriber).unwrap();
}

/// This macro computes the name of the function in which it is called.
/// We adapted it from:
/// <https://stackoverflow.com/questions/38088067/equivalent-of-func-or-function-in-rust>
/// Note that we can't define it in macros due to technical reasons
#[macro_export]
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
#[macro_export]
macro_rules! trace {
    ($($arg:tt)+) => {{
        use colored::Colorize;
        let msg = format!($($arg)+);
        log::trace!("[{}]:\n{}", $crate::function_name!().yellow(), msg)
    }};
    () => {{
        use colored::Colorize;
        log::trace!("[{}]", $crate::function_name!().yellow())
    }};
}

/// A custom log error macro. Uses the log crate.
#[macro_export]
macro_rules! error {
    ($($arg:tt)+) => {{
        use colored::Colorize;
        let msg = format!($($arg)+);
        log::error!("[{}]:\n{}", $crate::function_name!().red(), msg)
    }};
}

/// A custom log warn macro. Uses the log crate.
#[macro_export]
macro_rules! warn {
    ($($arg:tt)+) => {{
        use colored::Colorize;
        let msg = format!($($arg)+);
        log::warn!("[{}]:\n{}", $crate::function_name!().yellow(), msg)
    }};
}

/// A custom log info macro. Uses the log crate.
#[macro_export]
macro_rules! info {
    ($($arg:tt)+) => {{
        use colored::Colorize;
        let msg = format!($($arg)+);
        // As for info we generally output simple messages, we don't insert
        // a breakline
        log::info!("[{}]: {}", $crate::function_name!().yellow(), msg)
    }};
    () => {{
        log::info!("[{}]", $crate::function_name!().yellow())
    }};
}
