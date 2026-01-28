//! This module contains type definitions that have no equivalent in
//! Rustc.

mod full_def;
mod impl_infos;
mod synthetic_items;
mod variant_infos;

pub use full_def::*;
pub use impl_infos::*;
pub use synthetic_items::*;
pub use variant_infos::*;
