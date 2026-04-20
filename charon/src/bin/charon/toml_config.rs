//! Processing of the contents of `[package.metadata.charon]` in `Cargo.toml`.
use charon_lib::options::{CliOpts, Preset};
use clap::ValueEnum;
use serde::Deserialize;

/// The struct used to define the options available under `[package.metadata.charon]` in
/// `Cargo.toml`. These all mirror the corresponding cli option.
#[derive(Debug, Default, Deserialize)]
pub struct TomlConfig {
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
    #[serde(default)]
    pub rustc: RustcTomlConfig,
    #[serde(default)]
    pub cargo: CargoTomlConfig,
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
    /// Scalar options (preset, start_from_attribute): CLI value wins if set; TOML value used
    /// otherwise. Boolean options: OR of CLI and TOML. List options: always merged (both combined).
    pub(crate) fn apply(self, mut config: CliOpts, cargo_args: &mut Vec<String>) -> CliOpts {
        if config.preset.is_none() {
            config.preset = self.preset.map(|s| {
                Preset::from_str(&s, true /* ignore_case */).unwrap_or_else(
                    |_| panic!("Unknown preset {s:?} in Cargo.toml. Valid values: aeneas, eurydice, soteria, old-defaults, raw-mir, tests"),
                )
            });
        }
        config.extract_opaque_bodies |= self.extract_opaque_bodies;
        config.start_from.extend(self.start_from);
        config
            .start_from_if_exists
            .extend(self.start_from_if_exists);
        if config.start_from_attribute.is_none() {
            config.start_from_attribute = self.start_from_attribute;
        }
        config.start_from_pub |= self.start_from_pub;
        config.hide_marker_traits |= self.hide_marker_traits;
        config.include.extend(self.include);
        config.opaque.extend(self.opaque);
        config.exclude.extend(self.exclude);
        config.rustc_args.extend(self.rustc.flags);
        cargo_args.extend(self.cargo.flags);
        config
    }
}

/// Read `[package.metadata.charon]` from `./Cargo.toml` if present.
pub(crate) fn read_toml() -> Option<TomlConfig> {
    trace!("Reading options from `[package.metadata.charon]` in `Cargo.toml`");
    let contents = std::fs::read_to_string("./Cargo.toml").ok()?;
    let full: toml::Value = toml::from_str(&contents).ok()?;
    let charon_meta = full.get("package")?.get("metadata")?.get("charon")?.clone();
    Some(charon_meta.try_into().unwrap())
}
