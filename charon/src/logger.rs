#![allow(dead_code)]

extern crate env_logger;

/// Initialize the logger. We use a custom initialization to add some
/// useful debugging information, including the line number in the file.
pub fn initialize_logger() {
    use chrono::offset::Local;
    use env_logger::fmt::Color;
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
        let path = record.module_path().unwrap_or("");
        let line = match record.line() {
            Some(l) => l.to_string(),
            None => "".to_string(),
        };

        // Style for the brackets (change the color)
        let mut bracket_style = buf.style();
        bracket_style.set_color(Color::Rgb(120, 120, 120));

        writeln!(
            buf,
            "{}{} {} {}:{}{} {}",
            bracket_style.value("["),
            Local::now().format("%H:%M:%S"), // Rk.: use "%Y-%m-%d" to also have the date
            buf.default_styled_level(record.level()), // Print the level with colors
            path,
            line,
            bracket_style.value("]"),
            record.args()
        )
    });

    builder.init();
}
