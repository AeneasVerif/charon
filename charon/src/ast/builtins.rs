//! This file contains information about the assumed functions/types/traits definitions
//!
//! **IMPORTANT**:
//! When checking whether names are equal to one of the reference names below,
//! we ignore the disambiguators (see [crate::names] and [crate::names_utils]).
// TODO: rename to "primitive"

use crate::ast;
use crate::names::*;
use crate::types::*;
use macros::EnumIsA;

// Built-in functions
// We treat this one specially in the `inline_local_panic_functions` pass. See there for details.
pub static EXPLICIT_PANIC_NAME: &[&str] = &["core", "panicking", "panic_explicit"];

/// We redefine identifiers for assumed functions here, instead of reusing the
/// identifiers from [ullbc_ast], because:
/// - some of the functions (the panic functions) will actually not be translated
///   to functions: there are thus missing identifiers.
/// - some of the ids here are actually traits, that we disambiguate later
/// TODO: merge with the other enum?
#[derive(Copy, Clone, EnumIsA)]
pub enum BuiltinFun {
    Panic,
    BoxNew,
}

impl BuiltinFun {
    /// Converts to the ullbc equivalent. Panics if `self` is `Panic` as this should be handled
    /// separately.
    pub fn to_ullbc_builtin_fun(self) -> ast::AssumedFunId {
        match self {
            BuiltinFun::BoxNew => ast::AssumedFunId::BoxNew,
            BuiltinFun::Panic => panic!(),
        }
    }
}

impl AssumedTy {
    pub fn get_name(self) -> Name {
        let name: &[_] = match self {
            AssumedTy::Box => &["alloc", "boxed", "Box"],
            AssumedTy::Str => &["Str"],
            AssumedTy::Array => &["Array"],
            AssumedTy::Slice => &["Slice"],
        };
        Name::from_path(name)
    }
}

/// When translating from MIR to ULLBC, we ignore some type parameters for some
/// assumed types.
/// For instance, many types like box or vec are parameterized (in MIR) by an allocator
/// (`std::alloc::Allocator`): we ignore it.
pub fn type_to_used_params(id: AssumedTy) -> Vec<bool> {
    match id {
        AssumedTy::Box => {
            vec![true, false]
        }
        AssumedTy::Str => {
            vec![]
        }
        AssumedTy::Array | AssumedTy::Slice => vec![true],
    }
}
