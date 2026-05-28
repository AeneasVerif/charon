//! This file contains information about the builtin functions/types/traits definitions
//!
//! **IMPORTANT**:
//! When checking whether names are equal to one of the reference names below,
//! we ignore the disambiguators (see [crate::names] and [crate::ast::names_utils]).
// TODO: rename to "primitive"

use crate::names::*;
use crate::types::*;

// Built-in functions
// We treat this one specially in the `inline_local_panic_functions` pass. See there for details.
pub static EXPLICIT_PANIC_NAME: &[&str] = &["core", "panicking", "panic_explicit"];

pub static BOX_ASSUME_INIT_INTO_VEC_UNSAFE: &str = "box_assume_init_into_vec_unsafe";

pub static BOX_WRITE: &str = "alloc::boxed::Box::write";

// The translated Charon name contains an inherent impl path element where the Rust path contains
// `Box`. `NamePattern` does not yet inspect inherent impl receiver types, so passes that match the
// translated name need this wildcarded pattern.
pub static BOX_WRITE_PATTERN: &str = "alloc::boxed::_::write";

impl BuiltinTy {
    pub fn get_name(self) -> Name {
        let name: &[_] = match self {
            BuiltinTy::Box => &["alloc", "boxed", "Box"],
            BuiltinTy::Str => &["Str"],
        };
        Name::from_path(name)
    }
}
