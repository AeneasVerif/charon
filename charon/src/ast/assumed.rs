//! This file contains information about the assumed functions/types/traits definitions
//!
//! **IMPORTANT**:
//! When checking whether names are equal to one of the reference names below,
//! we ignore the disambiguators (see [crate::names] and [crate::names_utils]).
// TODO: rename to "primitive"

use crate::names::*;
use crate::types::*;
use crate::ullbc_ast;
use macros::EnumIsA;

/// Ignore the builtin/auto traits like [core::marker::Sized] or [core::marker::Sync].
pub const IGNORE_BUILTIN_MARKER_TRAITS: bool = true;

// Ignored traits (includes marker traits, and others)
pub static MARKER_SIZED_NAME: [&str; 3] = ["core", "marker", "Sized"];
pub static MARKER_TUPLE_NAME: [&str; 3] = ["core", "marker", "Tuple"];
pub static SYNC_NAME: [&str; 3] = ["core", "marker", "SYNC"];
pub static SEND_NAME: [&str; 3] = ["core", "marker", "SEND"];
pub static UNPIN_NAME: [&str; 3] = ["core", "marker", "UNPIN"];
pub static ALLOC_ALLOCATOR: [&str; 3] = ["core", "alloc", "Allocator"];
pub static IGNORED_TRAITS_NAMES: [&[&str]; 6] = [
    &MARKER_SIZED_NAME,
    &MARKER_TUPLE_NAME,
    &SYNC_NAME,
    &SEND_NAME,
    &UNPIN_NAME,
    &ALLOC_ALLOCATOR,
];

// Assumed types
pub static BOX_NAME: [&str; 3] = ["alloc", "boxed", "Box"];

// Assumed functions
// Pointers
pub static PTR_UNIQUE_NAME: [&str; 3] = ["core", "ptr", "Unique"];
pub static PTR_NON_NULL_NAME: [&str; 3] = ["core", "ptr", "NonNull"];

/// We redefine identifiers for assumed functions here, instead of reusing the
/// identifiers from [ullbc_ast], because:
/// - some of the functions (the panic functions) will actually not be translated
///   to functions: there are thus missing identifiers.
/// - some of the ids here are actually traits, that we disambiguate later
/// TODO: merge with the other enum?
#[derive(Copy, Clone, EnumIsA)]
pub(crate) enum BuiltinFun {
    Panic,
    BoxNew,
    BoxFree,
}

pub struct FunInfo {
    pub used_type_params: Vec<bool>,
    // TODO: rename. "value_args"?
    pub used_args: Vec<bool>,
}

impl BuiltinFun {
    /// Converts to the ullbc equivalent. Panics if `self` is `Panic` as this should be handled
    /// separately.
    pub(crate) fn to_ullbc_builtin_fun(self) -> ullbc_ast::AssumedFunId {
        match self {
            BuiltinFun::BoxNew => ullbc_ast::AssumedFunId::BoxNew,
            BuiltinFun::BoxFree => ullbc_ast::AssumedFunId::BoxFree,
            BuiltinFun::Panic => panic!(),
        }
    }

    /// Parse a name to recognize built-in functions.
    pub(crate) fn parse_name(name: &Name) -> Option<Self> {
        if name.equals_ref_name(&["core", "panicking", "panic"])
            || name.equals_ref_name(&["core", "panicking", "panic_fmt"])
            || name.equals_ref_name(&["std", "panicking", "begin_panic"])
            || name.equals_ref_name(&["std", "rt", "begin_panic"])
            || name.equals_ref_name(&["core", "panicking", "assert_failed"])
        {
            Some(BuiltinFun::Panic)
        } else if name.equals_ref_name(&["alloc", "alloc", "box_free"]) {
            Some(BuiltinFun::BoxFree)
        } else {
            // Box::new is peculiar because there is an impl block
            use PathElem::*;
            match name.name.as_slice() {
                [Ident(alloc, _), Ident(boxed, _), Impl(impl_elem), Ident(new, _)] => {
                    if alloc == "alloc" && boxed == "boxed" && new == "new" {
                        match &impl_elem.kind {
                            ImplElemKind::Ty(Ty::Adt(
                                TypeId::Assumed(AssumedTy::Box),
                                generics,
                            )) => {
                                let GenericArgs {
                                    regions,
                                    types,
                                    const_generics,
                                    trait_refs,
                                } = generics;
                                if regions.is_empty()
                                    && types.len() == 1
                                    && const_generics.is_empty()
                                    && trait_refs.is_empty()
                                {
                                    match types.as_slice() {
                                        [Ty::TypeVar(_)] => Some(BuiltinFun::BoxNew),
                                        _ => None,
                                    }
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }

    /// See the comments for [type_to_used_params]
    pub(crate) fn to_fun_info(self) -> Option<FunInfo> {
        match self {
            BuiltinFun::Panic => None,
            BuiltinFun::BoxNew => None,
            BuiltinFun::BoxFree => Some(FunInfo {
                used_type_params: vec![true, false],
                used_args: vec![true, false],
            }),
        }
    }
}

pub fn is_marker_trait(name: &Name) -> bool {
    for n in IGNORED_TRAITS_NAMES {
        if name.equals_ref_name(n) {
            return true;
        }
    }
    false
}

pub fn get_type_id_from_name(name: &Name) -> Option<AssumedTy> {
    if name.equals_ref_name(&BOX_NAME) {
        Some(AssumedTy::Box)
    } else if name.equals_ref_name(&PTR_UNIQUE_NAME) {
        Some(AssumedTy::PtrUnique)
    } else if name.equals_ref_name(&PTR_NON_NULL_NAME) {
        Some(AssumedTy::PtrNonNull)
    } else {
        None
    }
}

pub fn get_name_from_type_id(id: AssumedTy) -> Vec<String> {
    match id {
        AssumedTy::Box => BOX_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::PtrUnique => PTR_UNIQUE_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::PtrNonNull => PTR_NON_NULL_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::Str => vec!["Str".to_string()],
        AssumedTy::Array => vec!["Array".to_string()],
        AssumedTy::Slice => vec!["Slice".to_string()],
    }
}

/// When translating from MIR to ULLBC, we ignore some type parameters for some
/// assumed types.
/// For instance, many types like box or vec are parameterized (in MIR) by an allocator
/// (`std::alloc::Allocator`): we ignore it.
pub fn type_to_used_params(name: &Name) -> Option<Vec<bool>> {
    trace!("{:?}", name);
    match get_type_id_from_name(name) {
        None => None,
        Some(id) => {
            let id = match id {
                AssumedTy::Box => {
                    vec![true, false]
                }
                AssumedTy::PtrUnique | AssumedTy::PtrNonNull => {
                    vec![true]
                }
                AssumedTy::Str => {
                    vec![]
                }
                AssumedTy::Array | AssumedTy::Slice => vec![true],
            };
            Some(id)
        }
    }
}
