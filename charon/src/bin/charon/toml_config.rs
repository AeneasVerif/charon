//! Processing of the contents of a `Charon.toml` file.
use charon_lib::options::{CliOpts, Preset};
use clap::ValueEnum;
use serde::Deserialize;
use std::path::PathBuf;

/// The struct used to define the options available in `Charon.toml` files.
#[derive(Debug, Deserialize)]
pub struct TomlConfig {
    #[serde(default)]
    pub charon: CharonTomlConfig,
    #[serde(default)]
    pub rustc: RustcTomlConfig,
    /// Extra arguments forwarded to `cargo build` (equivalent to flags after `--`).
    #[serde(default)]
    pub cargo: CargoTomlConfig,
}

/// The struct used to define the options available in `Charon.toml` files. These all mirror the
/// corresponding cli option.
#[derive(Debug, Default, Deserialize)]
pub struct CharonTomlConfig {
    /// Corresponds to `--preset`. Use the same names as the CLI (e.g. `"aeneas"`).
    #[serde(default)]
    pub preset: Option<String>,
    #[serde(default)]
    pub extract_opaque_bodies: bool,
    #[serde(default)]
    pub start_from: Vec<String>,
    #[serde(default)]
    pub start_from_if_exists: Vec<String>,
    #[serde(default)]
    pub start_from_attribute: Option<String>,
    #[serde(default)]
    pub start_from_pub: bool,
    #[serde(default)]
    pub hide_marker_traits: bool,
    #[serde(default)]
    pub include: Vec<String>,
    #[serde(default)]
    pub opaque: Vec<String>,
    #[serde(default)]
    pub exclude: Vec<String>,
}

#[derive(Debug, Default, Deserialize)]
pub struct RustcTomlConfig {
    #[serde(default)]
    pub flags: Vec<String>,
}

/// Extra arguments forwarded to `cargo build` (equivalent to flags after `--`).
#[derive(Debug, Default, Deserialize)]
pub struct CargoTomlConfig {
    #[serde(default)]
    pub flags: Vec<String>,
}

impl TomlConfig {
    /// Applies the options specified in the toml file to the cli options and cargo args.
    /// In case of conflict, cli options take precedence.
    pub(crate) fn apply(self, mut config: CliOpts, cargo_args: &mut Vec<String>) -> CliOpts {
        if config.preset.is_none() {
            config.preset = self.charon.preset.map(|s| {
                Preset::from_str(&s, true /* ignore_case */).unwrap_or_else(
                    |_| panic!("Unknown preset {s:?} in Charon.toml. Valid values: aeneas, eurydice, soteria, old-defaults, raw-mir, tests"),
                )
            });
        }
        config.extract_opaque_bodies |= self.charon.extract_opaque_bodies;
        config.start_from.extend(self.charon.start_from);
        config
            .start_from_if_exists
            .extend(self.charon.start_from_if_exists);
        if config.start_from_attribute.is_none() {
            config.start_from_attribute = self.charon.start_from_attribute;
        }
        config.start_from_pub |= self.charon.start_from_pub;
        config.hide_marker_traits |= self.charon.hide_marker_traits;
        config.include.extend(self.charon.include);
        config.opaque.extend(self.charon.opaque);
        config.exclude.extend(self.charon.exclude);
        config.rustc_args.extend(self.rustc.flags);
        cargo_args.extend(self.cargo.flags);
        config
    }
}

/// Read `./Charon.toml` if there is such a file.
pub(crate) fn read_toml() -> Option<TomlConfig> {
    trace!("Reading options from the `Charon.toml` file");
    let path = PathBuf::from("./Charon.toml");
    if path.exists() {
        let contents = std::fs::read_to_string(path).unwrap();
        Some(toml::from_str(&contents).unwrap())
    } else {
        None
    }
}
