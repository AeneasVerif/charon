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

impl BuiltinTy {
    pub fn get_name(self) -> Name {
        let name: &[_] = match self {
            BuiltinTy::Box => &["alloc", "boxed", "Box"],
            BuiltinTy::Str => &["Str"],
            BuiltinTy::Array => &["Array"],
            BuiltinTy::Slice => &["Slice"],
        };
        Name::from_path(name)
    }
}

/// When translating from MIR to ULLBC, we ignore some type parameters for some builtin types.
/// For instance, many types like box or vec are parameterized (in MIR) by an allocator
/// (`std::alloc::Allocator`): we ignore it.
pub fn type_to_used_params(id: BuiltinTy) -> Vec<bool> {
    match id {
        BuiltinTy::Box => {
            vec![true, false]
        }
        BuiltinTy::Str => {
            vec![]
        }
        BuiltinTy::Array | BuiltinTy::Slice => vec![true],
    }
}
