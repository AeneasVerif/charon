extern crate proc_macro;
use proc_macro::TokenStream;

/// This is a dummy attribute
#[proc_macro_attribute]
pub fn assume(attr: TokenStream, item: TokenStream) -> TokenStream {
    // There shouldn't be any attributes
    assert!(attr.is_empty());
    // This macro doesn't do anything: we simply return the definition
    item
}
