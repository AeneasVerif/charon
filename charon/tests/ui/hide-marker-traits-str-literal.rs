//@ charon-args=--hide-marker-traits
// `str` must stay unsized when hiding marker traits, otherwise borrowed string literals get
// evaluated into a local and we return a dangling reference.

fn ret_str() -> &'static str {
    "hello"
}
