//! Processing of the contents of `[package.metadata.charon]` in `Cargo.toml`.
use charon_lib::options::CliOpts;
use serde::Deserialize;

/// The struct used to define the options available under `[package.metadata.charon]` in
/// `Cargo.toml`. These all mirror the corresponding cli option.
#[derive(Debug, Default, Deserialize)]
pub struct TomlConfig {
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
}

#[derive(Debug, Default, Deserialize)]
pub struct RustcTomlConfig {
    #[serde(default)]
    pub flags: Vec<String>,
}

impl TomlConfig {
    /// Applies the options specified in the toml file to the cli options. In case of conflict, cli
    /// options take precedence.
    pub(crate) fn apply(self, mut config: CliOpts) -> CliOpts {
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
