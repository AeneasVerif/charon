//! Lightweight, opt-in timing instrumentation.
//!
//! Enabled by setting the `CHARON_TIMINGS` environment variable. Set it to `1` to get a
//! human-readable report on stderr at the end of the run; set it to a file path to additionally
//! append the measurements as csv lines to that file.
//!
//! Scopes can be nested: we report both the total (wall) time spent in a scope and the "self"
//! time, i.e. the time not spent inside a nested instrumented scope.
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::sync::{LazyLock, Mutex};
use std::time::{Duration, Instant};

/// Whether timing is enabled at all.
static SETTING: LazyLock<Option<String>> = LazyLock::new(|| std::env::var("CHARON_TIMINGS").ok());

pub fn enabled() -> bool {
    SETTING.is_some()
}

#[derive(Default, Clone, Copy)]
pub struct Measure {
    pub total: Duration,
    pub own: Duration,
    pub count: u64,
}

/// Measurements are aggregated globally (translation is single-threaded but rustc may call us from
/// several threads, hence the mutex).
static MEASURES: LazyLock<Mutex<HashMap<String, Measure>>> = LazyLock::new(Default::default);

thread_local! {
    /// Time spent in nested scopes, for the currently-running scope.
    static NESTED: RefCell<Vec<Duration>> = const { RefCell::new(Vec::new()) };
}

/// A running measurement; the timing is recorded when this is dropped.
pub struct Guard {
    name: &'static str,
    /// Only used to give a more precise name than `name` when relevant.
    suffix: Option<String>,
    start: Instant,
}

/// Time the given scope, if timings are enabled.
pub fn scope(name: &'static str) -> Option<Guard> {
    scope_with(name, None)
}

/// Same as [`scope`] but allows refining the name dynamically.
pub fn scope_with(name: &'static str, suffix: Option<String>) -> Option<Guard> {
    if !enabled() {
        return None;
    }
    NESTED.with_borrow_mut(|stack| stack.push(Duration::ZERO));
    Some(Guard {
        name,
        suffix,
        start: Instant::now(),
    })
}

impl Drop for Guard {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed();
        let nested = NESTED.with_borrow_mut(|stack| {
            let nested = stack.pop().unwrap_or_default();
            if let Some(parent) = stack.last_mut() {
                *parent += elapsed;
            }
            nested
        });
        let long_key = self
            .suffix
            .as_ref()
            .map(|suffix| format!("{}/{suffix}", self.name));
        let key: &str = long_key.as_deref().unwrap_or(self.name);
        let mut measures = MEASURES.lock().unwrap();
        // Avoid allocating a fresh `String` on each call.
        if !measures.contains_key(key) {
            measures.insert(key.to_owned(), Measure::default());
        }
        let entry = measures.get_mut(key).unwrap();
        entry.total += elapsed;
        entry.own += elapsed.saturating_sub(nested);
        entry.count += 1;
    }
}

/// Same as [`scope_with`] but only computes the suffix if timings are enabled.
pub fn scope_lazy(name: &'static str, suffix: impl FnOnce() -> String) -> Option<Guard> {
    if !enabled() {
        return None;
    }
    scope_with(name, Some(suffix()))
}

/// Time the given closure.
pub fn time<T>(name: &'static str, f: impl FnOnce() -> T) -> T {
    let _guard = scope(name);
    f()
}

/// Print the timing report on stderr, and append it to the file given in `CHARON_TIMINGS` if it
/// isn't `1`.
pub fn report(crate_name: &str) {
    let Some(setting) = SETTING.as_ref() else {
        return;
    };
    let measures = MEASURES.lock().unwrap();
    let mut entries: Vec<(&String, &Measure)> = measures.iter().collect();
    entries.sort_by_key(|(name, m)| (std::cmp::Reverse(m.own), (*name).clone()));

    let mut out = String::new();
    out += &format!("\n=== charon timings for crate `{crate_name}` ===\n");
    out += &format!(
        "{:<60} {:>12} {:>12} {:>10}\n",
        "scope", "total (ms)", "self (ms)", "calls"
    );
    for (name, m) in &entries {
        out += &format!(
            "{:<60} {:>12.2} {:>12.2} {:>10}\n",
            name,
            m.total.as_secs_f64() * 1000.,
            m.own.as_secs_f64() * 1000.,
            m.count
        );
    }
    eprint!("{out}");

    if setting != "1"
        && let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(setting)
    {
        for (name, m) in &entries {
            let _ = writeln!(
                file,
                "{crate_name},{name},{:.3},{:.3},{}",
                m.total.as_secs_f64() * 1000.,
                m.own.as_secs_f64() * 1000.,
                m.count
            );
        }
    }
}
