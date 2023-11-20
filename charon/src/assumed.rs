//! This file contains information about the assumed functions/types/traits definitions
//!
//! **IMPORTANT**:
//! When checking whether names are equal to one of the reference names below,
//! we ignore the disambiguators (see [crate::names] and [crate::names_utils]).
// TODO: rename to "primitive"
#![allow(dead_code)]

use crate::names::*;
use crate::types::*;
use crate::ullbc_ast;
use macros::EnumIsA;

/// Ignore the builtin/auto traits like [core::marker::Sized] or [core::marker::Sync].
pub const IGNORE_BUILTIN_MARKER_TRAITS: bool = true;

// Ignored traits (includes marker traits, and others)
pub static SIZED_NAME: [&str; 3] = ["core", "marker", "Sized"];
pub static MARKER_TUPLE_NAME: [&str; 3] = ["core", "marker", "Tuple"];
pub static SYNC_NAME: [&str; 3] = ["core", "marker", "SYNC"];
pub static SEND_NAME: [&str; 3] = ["core", "marker", "SEND"];
pub static UNPIN_NAME: [&str; 3] = ["core", "marker", "UNPIN"];
pub static ALLOC_ALLOCATOR: [&str; 3] = ["core", "alloc", "Allocator"];
pub static IGNORED_TRAITS_NAMES: [&[&str]; 6] = [
    &SIZED_NAME,
    &MARKER_TUPLE_NAME,
    &SYNC_NAME,
    &SEND_NAME,
    &UNPIN_NAME,
    &ALLOC_ALLOCATOR,
];

// Assumed types
pub static BOX_NAME: [&str; 3] = ["alloc", "boxed", "Box"];

pub static OPTION_NONE_VARIANT_ID: VariantId::Id = VariantId::ZERO;
pub static OPTION_SOME_VARIANT_ID: VariantId::Id = VariantId::ONE;

//
// Assumed functions
//
pub static PANIC_NAME: [&str; 3] = ["core", "panicking", "panic"];
pub static BEGIN_PANIC_NAME: [&str; 3] = ["std", "panicking", "begin_panic"];
pub static ASSERT_FAILED_NAME: [&str; 3] = ["core", "panicking", "assert_failed"];

// Boxes - remark: there misses `Box::new` which has an impl block (TODO: remove?)
// Only Box::free needs to have a special treatment.
pub static BOX_FREE_NAME: [&str; 3] = ["alloc", "alloc", "box_free"];

// Pointers
pub static PTR_UNIQUE_NAME: [&str; 3] = ["core", "ptr", "Unique"];
pub static PTR_NON_NULL_NAME: [&str; 3] = ["core", "ptr", "NonNull"];

// We ignore this trait, which is automatically added for some type parameters
// when defining a new type.
pub static MARKER_SIZED_NAME: [&str; 3] = ["core", "marker", "Sized"];

/// We redefine identifiers for assumed functions here, instead of reusing the
/// identifiers from [ullbc_ast], because:
/// - some of the functions (the panic functions) will actually not be translated
///   to functions: there are thus missing identifiers.
/// - some of the ids here are actually traits, that we disambiguate later
/// TODO: merge with the other enum?
#[derive(EnumIsA)]
enum FunId {
    /// `core::panicking::panic`
    Panic,
    /// `std::panicking::begin_panic` - TODO: remove?
    BeginPanic,
    BoxNew,
    BoxFree,
}

pub fn is_marker_trait(name: &Name) -> bool {
    for n in IGNORED_TRAITS_NAMES {
        if name.equals_ref_name(n) {
            return true;
        }
    }
    false
}

pub fn get_type_id_from_name(name: &TypeName) -> Option<AssumedTy> {
    if name.equals_ref_name(&BOX_NAME) {
        Option::Some(AssumedTy::Box)
    } else if name.equals_ref_name(&PTR_UNIQUE_NAME) {
        Option::Some(AssumedTy::PtrUnique)
    } else if name.equals_ref_name(&PTR_NON_NULL_NAME) {
        Option::Some(AssumedTy::PtrNonNull)
    } else {
        Option::None
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

fn get_fun_id_from_name_full(name: &FunName) -> Option<FunId> {
    if name.equals_ref_name(&PANIC_NAME) {
        Option::Some(FunId::Panic)
    } else if name.equals_ref_name(&BEGIN_PANIC_NAME) {
        Option::Some(FunId::BeginPanic)
    } else if name.equals_ref_name(&BOX_FREE_NAME) {
        Option::Some(FunId::BoxFree)
    } else {
        // Box::new is peculiar because there is an impl block
        use PathElem::*;
        match name.name.as_slice() {
            [Ident(alloc, _), Ident(boxed, _), Impl(impl_elem), Ident(new, _)] => {
                if alloc == "alloc" && boxed == "boxed" && new == "new" {
                    match &impl_elem.ty {
                        Ty::Adt(TypeId::Assumed(AssumedTy::Box), generics) => {
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
                                    [Ty::TypeVar(_)] => Option::Some(FunId::BoxNew),
                                    _ => Option::None,
                                }
                            } else {
                                Option::None
                            }
                        }
                        _ => Option::None,
                    }
                } else {
                    Option::None
                }
            }
            _ => Option::None,
        }
    }
}

pub fn get_fun_id_from_name(name: &FunName) -> Option<ullbc_ast::AssumedFunId> {
    match get_fun_id_from_name_full(name) {
        Option::Some(id) => {
            let id = match id {
                FunId::Panic | FunId::BeginPanic => unreachable!(),
                FunId::BoxNew => ullbc_ast::AssumedFunId::BoxNew,
                FunId::BoxFree => ullbc_ast::AssumedFunId::BoxFree,
            };
            Option::Some(id)
        }
        Option::None => Option::None,
    }
}

/// When translating from MIR to ULLBC, we ignore some type parameters for some
/// assumed types.
/// For instance, many types like box or vec are parameterized (in MIR) by an allocator
/// (`std::alloc::Allocator`): we ignore it.
pub fn type_to_used_params(name: &TypeName) -> Option<Vec<bool>> {
    trace!("{:?}", name);
    match get_type_id_from_name(name) {
        Option::None => Option::None,
        Option::Some(id) => {
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
            Option::Some(id)
        }
    }
}

pub struct FunInfo {
    pub used_type_params: Vec<bool>,
    // TODO: rename. "value_args"?
    pub used_args: Vec<bool>,
}

/// See the comments for [type_to_used_params]
pub fn function_to_info(name: &FunName) -> Option<FunInfo> {
    trace!("{:?}", name);
    match get_fun_id_from_name_full(name) {
        Option::None => Option::None,
        Option::Some(id) => {
            let info = match id {
                FunId::Panic => FunInfo {
                    used_type_params: vec![],
                    used_args: vec![true],
                },
                FunId::BeginPanic => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true],
                },
                FunId::BoxNew => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true],
                },
                FunId::BoxFree => FunInfo {
                    used_type_params: vec![true, false],
                    used_args: vec![true, false],
                },
            };
            Option::Some(info)
        }
    }
}
