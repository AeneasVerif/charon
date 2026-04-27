// feature_fn is only compiled when my_feature is enabled.
// It appears in the charon output only if [package.metadata.charon.cargo] flags in Cargo.toml
// correctly forwarded --features my_feature to cargo build.
#[cfg(feature = "my_feature")]
pub fn feature_fn() -> u32 {
    42
}

fn main() {}
