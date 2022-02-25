//! Defines some utilities for the variables
#![allow(dead_code)]

use crate::names::*;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::DefPathData;
use rustc_middle::ty::TyCtxt;
use serde::{Serialize, Serializer};

impl Name {
    pub fn from(name: Vec<String>) -> Name {
        Name { name: name }
    }

    pub fn to_vec(self) -> Vec<String> {
        self.name
    }

    pub fn len(&self) -> usize {
        self.name.len()
    }

    /// Compare the name to a constant array
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        if self.name.len() != ref_name.len() {
            return false;
        }

        for i in 0..self.name.len() {
            if self.name[i] != ref_name[i] {
                return false;
            }
        }
        return true;
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.name.join("::"))
    }
}

impl Serialize for Name {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use crate::common::*;
        let name = VecSerializer::new(&self.name);
        name.serialize(serializer)
    }
}

fn module_ident_equals_ref_name(module: &Name, ident: &String, ref_name: &[&str]) -> bool {
    if module.len() + 1 != ref_name.len() {
        return false;
    }

    for i in 0..module.len() {
        if module.name[i] != ref_name[i] {
            return false;
        }
    }
    let i = module.len();
    return ident == ref_name[i];
}

impl FunName {
    /// Compare the name to a constant array
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        match self {
            FunName::Regular(name) => name.equals_ref_name(ref_name),
            FunName::Impl(type_name, _impl_id, ident) => {
                // TODO: we ignore the impl id, which is not good
                // At some point, we will have to make some of the primitive
                // functions (the ones for the vectors, more specifically)
                // non-primitive, and always return false in this branch.
                module_ident_equals_ref_name(type_name, ident, ref_name)
            }
        }
    }
}

impl std::fmt::Display for FunName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            FunName::Regular(name) => {
                write!(f, "{}", name)
            }
            FunName::Impl(type_name, impl_id, ident) => {
                write!(f, "{}{{{}}}::{}", type_name, impl_id, ident)
            }
        }
    }
}

/// Compute a name from a type [`DefId`](DefId).
///
/// This only works for def ids coming from types! For values, it is a bit
/// more complex.
pub fn type_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> TypeName {
    trace!("{:?}", def_id);

    let def_path = tcx.def_path(def_id);
    let crate_name = tcx.crate_name(def_id.krate).to_string();

    trace!("def path: {:?}", def_path);
    let mut name: Vec<String> = vec![crate_name];
    for path in def_path.data.iter() {
        // The path disambiguator may be <> 0, but I'm not sure in which cases
        // nor how to handle that case. For sanity, we thus check that it is
        // equal to 0.
        assert!(path.disambiguator == 0);
        match &path.data {
            rustc_hir::definitions::DefPathData::TypeNs(symbol) => {
                name.push(symbol.to_ident_string());
            }
            _ => {
                trace!("unexpected DefPathData: {:?}", &path.data);
                unreachable!();
            }
        }
    }

    trace!("resulting name: {:?}", &name);

    TypeName::from(name)
}

fn defpathdata_to_value_ns(data: DefPathData) -> Option<String> {
    match data {
        // The def path data should be in the value namespace
        rustc_hir::definitions::DefPathData::ValueNs(symbol) => Some(symbol.to_ident_string()),
        _ => {
            trace!("Unexpected DefPathData: {:?}", data);
            None
        }
    }
}

fn defpathdata_to_type_ns(data: DefPathData) -> Option<String> {
    match data {
        // The def path data should be in the type namespace
        rustc_hir::definitions::DefPathData::TypeNs(symbol) => Some(symbol.to_ident_string()),
        _ => {
            trace!("Unexpected DefPathData: {:?}", data);
            None
        }
    }
}

/// Retrieve the function name from a `DefId`.
pub fn function_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> FunName {
    trace!("{:?}", def_id);

    // We have to be a bit careful when retrieving the name. For instance, due
    // to reexports, [`TyCtxt::def_path_str`](TyCtxt::def_path_str) might give
    // different names depending on the def id on which it is called, even though
    // those def ids might actually identify the same definition.
    // For instance: `std::boxed::Box` and `alloc::boxed::Box` are actually
    // the same (the first one is a reexport).
    // This is why we implement a custom function to retrieve the original name.

    // There are two cases:
    // - either the function is a top-level function, and we simply convert
    //   every element of the path to a string.
    // - or it is a function in an `impl` block, in which case we retrieve the
    //   function name (ex.: "new") and append it to the type name from which
    //   the `impl` block is a child (ex.: "alloc::boxed::Box"). Note that the
    //   way we convert the path to a name gives us the "original" name, before
    //   reexports.
    // In order to distinguish the cases, we use the definition key, which
    // combines the parent def index (from which we reconstruct a def id to
    // retrieve its path) with some path data. We then check the parent's key
    // data to see if it is an `Impl`.
    // Note that those peculiarities only apply to values: types can't be defined
    // in impl blocks.
    let def_key = tcx.def_key(def_id);

    // Reconstruct the parent def id: it's the same as the function's def id,
    // at the exception of the index.
    let parent_def_id = DefId {
        index: def_key.parent.unwrap(),
        ..def_id
    };

    // Retrieve the parent's key
    let parent_def_key = tcx.def_key(parent_def_id);

    // Not sure what to do with the disambiguator yet, so for now I check that
    // it is always equal to 0, in case of local functions.
    // Rk.: I think there is a unique disambiguator per `impl` block.
    assert!(!def_id.is_local() || parent_def_key.disambiguated_data.disambiguator == 0);

    // Check the parent key
    match parent_def_key.disambiguated_data.data {
        rustc_hir::definitions::DefPathData::Impl => {
            // The parent is an `impl` block: use the parent path.
            // This is a bit indirect, but in order to get a usable parent
            // path, we need to retrieve the type of the impl block (it actually
            // gives the type the impl block was defined for). This type should
            // be an ADT, because it was user defined. We can then retrieve
            // its def id, and convert it to a path (which is simpler, because
            // types can't be defined in impl blocks).
            let parent_type = tcx.type_of(parent_def_id);

            // Retrieve the parent type name
            let type_name = match parent_type.kind() {
                rustc_middle::ty::TyKind::Adt(adt_def, _) => {
                    // We can compute the type's name
                    type_def_id_to_name(tcx, adt_def.did)
                }
                _ => {
                    unreachable!();
                }
            };

            // Retrieve the function name
            let impl_id = ImplId::Id::new(def_key.disambiguated_data.disambiguator as usize);
            let fun_name = defpathdata_to_value_ns(def_key.disambiguated_data.data).unwrap();

            return FunName::Impl(type_name, impl_id, fun_name);
        }
        rustc_hir::definitions::DefPathData::TypeNs(_ns) => {
            // Not an `impl` block.
            // The function can be a trait function, like: `std::ops::Deref::deref`
            // Translating the parent path is straightforward: it should be a type path.
            let mut name = type_def_id_to_name(tcx, parent_def_id).to_vec();
            trace!("parent name: {:?}", name);

            // Retrieve the function name
            assert!(def_key.disambiguated_data.disambiguator == 0);
            name.push(defpathdata_to_value_ns(def_key.disambiguated_data.data).unwrap());
            let name = Name::from(name);
            FunName::Regular(name)
        }
        rustc_hir::definitions::DefPathData::CrateRoot => {
            // Top-level function
            let crate_name = tcx.crate_name(def_id.krate).to_ident_string();
            let name = Name::from(vec![
                crate_name,
                defpathdata_to_value_ns(def_key.disambiguated_data.data).unwrap(),
            ]);
            return FunName::Regular(name);
        }
        _ => {
            trace!(
                "DefId {:?}: Unexpected DefPathData: {:?}",
                def_id,
                parent_def_key.disambiguated_data.data
            );
            unreachable!();
        }
    }
}

/// Retrieve the trait name from a `DefId`.
/// TODO: very similar to [function_def_id_to_name] (see the comments).
/// We may want to factorize at some point.
pub fn trait_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> FunName {
    trace!("{:?}", def_id);

    let def_key = tcx.def_key(def_id);

    // Reconstruct the parent def id: it's the same as the function's def id,
    // at the exception of the index.
    let parent_def_id = DefId {
        index: def_key.parent.unwrap(),
        ..def_id
    };

    // Retrieve the parent's key
    let parent_def_key = tcx.def_key(parent_def_id);

    // Not sure what to do with the disambiguator yet, so for now I check that
    // it is always equal to 0, in case of local functions.
    // Rk.: I think there is a unique disambiguator per `impl` block.
    assert!(!def_id.is_local() || parent_def_key.disambiguated_data.disambiguator == 0);

    // Check the parent key
    match parent_def_key.disambiguated_data.data {
        rustc_hir::definitions::DefPathData::TypeNs(_ns) => {
            // Not an `impl` block.
            // The function can be a trait function, like: `std::ops::Deref::deref`
            // Translating the parent path is straightforward: it should be a type path.
            let mut name = type_def_id_to_name(tcx, parent_def_id).to_vec();
            trace!("parent name: {:?}", name);

            // Retrieve the function name
            assert!(def_key.disambiguated_data.disambiguator == 0);
            name.push(defpathdata_to_type_ns(def_key.disambiguated_data.data).unwrap());
            let name = Name::from(name);
            FunName::Regular(name)
        }
        _ => {
            trace!(
                "DefId {:?}: Unexpected DefPathData: {:?}",
                def_id,
                parent_def_key.disambiguated_data.data
            );
            unreachable!();
        }
    }
}
