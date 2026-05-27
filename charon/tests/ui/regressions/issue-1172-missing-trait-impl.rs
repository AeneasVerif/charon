//@ charon-args=--preset=aeneas
//@ no-default-options
// The `Default` impl indirectly uses the one for `[[u8; 16]; 29]`, but that impl doesn't end up in
// `ordered_decls` because it's unused.
#[derive(Default)]
pub struct Key {
    round_keys: [[u8; 16]; 29],
}
