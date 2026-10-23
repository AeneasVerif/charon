#![allow(rustdoc::private_intra_doc_links)]
#![allow(clippy::unneeded_struct_pattern, clippy::should_implement_trait)]

mod rustc_utils;
pub mod state;

mod constant_utils;
mod types;

mod prelude;

pub use prelude::*;

mod sinto;
mod traits;

pub use hax_adt_into::AdtInto;
pub use sinto::SInto;

pub mod options {
    pub use rustc_trait_elaboration::BoundsOptions;

    #[derive(Debug, Default, Clone)]
    pub struct Options {
        /// Whether we should evaluate and inline the value of anonymous constants (inline `const {}`
        /// blocks or advanced constant expressions as in `[T; N+1]`), or refer to them as
        /// `GlobalName`s.
        pub inline_anon_consts: bool,
        /// How to read evaluated constants.
        pub consts: rustc_const_uneval::Config,
    }
}
