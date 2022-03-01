//! Defines some utilities for the variables
//!
//! For now, we have one function per object kind (type, trait, function,
//! module): many of them could be factorized (will do).
#![allow(dead_code)]

use crate::names::*;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::DefPathData;
use rustc_hir::{Item, ItemKind};
use rustc_middle::ty::TyCtxt;
use serde::{Serialize, Serializer};
use std::collections::HashSet;

impl PathElem {
    // TODO: we could make that an eq trait?
    // On the other hand I'm not fond of overloading...
    fn equals_ident(&self, id: &str) -> bool {
        match self {
            PathElem::Ident(s) => {
                return s == id;
            }
            PathElem::Disambiguator(_) => {
                return false;
            }
        }
    }
}

impl std::fmt::Display for PathElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            PathElem::Ident(s) => {
                write!(f, "{}", s)
            }
            PathElem::Disambiguator(d) => {
                write!(f, "{}", d)
            }
        }
    }
}

impl Name {
    pub fn from(name: Vec<String>) -> Name {
        Name {
            name: name.into_iter().map(|s| PathElem::Ident(s)).collect(),
        }
    }

    pub fn len(&self) -> usize {
        self.name.len()
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    ///
    /// [equal]: if `true`, check that the name is equal to the ref. If `false`:
    /// only check if the ref is a prefix of the name.
    pub fn compare_with_ref_name(&self, equal: bool, ref_name: &[&str]) -> bool {
        let name: Vec<&PathElem> = self.name.iter().filter(|e| e.is_ident()).collect();

        if name.len() < ref_name.len() || (equal && name.len() != ref_name.len()) {
            return false;
        }

        for i in 0..ref_name.len() {
            if !name[i].equals_ident(&ref_name[i]) {
                return false;
            }
        }
        return true;
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        self.compare_with_ref_name(true, ref_name)
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    pub fn prefix_is_same(&self, ref_name: &[&str]) -> bool {
        self.compare_with_ref_name(false, ref_name)
    }

    /// Return `true` if the name identifies an item inside the module: `krate::module`
    pub fn is_in_module(&self, krate: &String, module: &String) -> bool {
        self.prefix_is_same(&[krate, module])
    }

    /// Similar to [is_in_module]
    pub fn is_in_modules(&self, krate: &String, modules: &HashSet<String>) -> bool {
        if self.len() >= 2 {
            match (&self.name[0], &self.name[1]) {
                (PathElem::Ident(s0), PathElem::Ident(s1)) => s0 == krate && modules.contains(s1),
                _ => false,
            }
        } else {
            false
        }
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        let v: Vec<String> = self.name.iter().map(|s| s.to_string()).collect();
        write!(f, "{}", v.join("::"))
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

/// Retrieve an item name from a `DefId`.
pub fn item_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> ItemName {
    trace!("{:?}", def_id);

    // We have to be a bit careful when retrieving names from def ids. For instance,
    // due to reexports, [`TyCtxt::def_path_str`](TyCtxt::def_path_str) might give
    // different names depending on the def id on which it is called, even though
    // those def ids might actually identify the same definition.
    // For instance: `std::boxed::Box` and `alloc::boxed::Box` are actually
    // the same (the first one is a reexport).
    // This is why we implement a custom function to retrieve the original name
    // (though this makes us loose aliases - we may want to investigate this
    // issue in the future).

    // We lookup the path associated to an id, and convert it to a name.
    // Paths very precisely identify where an item is. There are important
    // subcases, like the items in an `Impl` block:
    // ```
    // impl<T> List<T> {
    //   fn new() ...
    // }
    // ```
    //
    // The path for the `new` function above will look like something like
    // this: `TypeNs("List") :: Impl :: ValueNs("new")`
    // (where "Ns" stands for "namespace").
    // As there may be several "impl" blocks for one type, each impl block is
    // identified by a unique number (rustc calls this a "disambiguator").
    // On our side, we consider "impl" and "impl trait" blocks only for the
    // disambiguator.
    //
    // Finally, there can't be nested `impl` (or "impl trait") blocks, and we
    // can't have modules inside of impls, etc.. We thus generate names of the
    // following shape:
    // - regular names (list of strings)
    // - names for items coming from impl blocks:
    //   (type name (list of strings), disambiguator (index), item name (list of strings))

    //   For instance, for the `new` function above:
    //   `(["List"], 0, ["new"])`

    // We build the name as follows:
    // - we push identifiers to the [name] vector below
    // - if we find an `Impl` block, we move [name] to [type_name], and set
    //   the [disambiguator] to `Some`, then continue pushing to [name]
    // - of course, we check that we never set [disambiguator] twice
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    let mut name: Vec<PathElem> = vec![PathElem::Ident(crate_name)];

    // Rk.: below we try to be as tight as possible with regards to sanity
    // checks, to make sure we understand what happens with def paths, and
    // fail whenever we get something which is even slightly outside what
    // we expect.
    let def_path = tcx.def_path(def_id);
    let mut i = 0;
    for path in def_path.data.iter() {
        match &path.data {
            DefPathData::TypeNs(symbol) => {
                assert!(path.disambiguator == 0); // Sanity check
                name.push(PathElem::Ident(symbol.to_ident_string()));
            }
            DefPathData::ValueNs(symbol) => {
                if path.disambiguator != 0 {
                    // I don't like that

                    // I think this only happens with names introduced by macros
                    // (though not sure). For instance:
                    // `betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}`
                    let s = symbol.to_ident_string();
                    assert!(s == "_");
                    name.push(PathElem::Ident(s));
                    name.push(PathElem::Disambiguator(Disambiguator::Id::new(
                        path.disambiguator as usize,
                    )));
                } else {
                    name.push(PathElem::Ident(symbol.to_ident_string()));
                }
            }
            DefPathData::CrateRoot => {
                assert!(path.disambiguator == 0); // Sanity check
                assert!(i == 0); // Sanity check
                                 // The name has been initialized with the crate name
            }
            DefPathData::Impl => {
                // We need the disambiguator
                name.push(PathElem::Disambiguator(Disambiguator::Id::new(
                    path.disambiguator as usize,
                )));
            }
            DefPathData::ImplTrait => {
                // TODO: this should work the same as for `Impl`
                unimplemented!();
            }
            DefPathData::MacroNs(symbol) => {
                assert!(path.disambiguator == 0); // Sanity check

                // There may be namespace collisions between, say, function
                // names and macros (not sure). However, this isn't much
                // of an issue here, because for now we don't expose macros
                // in the AST, and only use macro names in [register], for
                // instance to filter opaque modules.
                name.push(PathElem::Ident(symbol.to_ident_string()));
            }
            _ => {
                error!("Unexpected DefPathData: {:?}", &path.data);
                unreachable!("Unexpected DefPathData: {:?}", &path.data);
            }
        }
        i += 1;
    }

    // Return
    Name { name }
}

pub fn type_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> TypeName {
    item_def_id_to_name(tcx, def_id)
}

pub fn module_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> ModuleName {
    item_def_id_to_name(tcx, def_id)
}

pub fn function_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> FunName {
    item_def_id_to_name(tcx, def_id)
}

pub fn trait_def_id_to_name(tcx: TyCtxt, def_id: DefId) -> FunName {
    item_def_id_to_name(tcx, def_id)
}

/// Returns an optional name for an HIR item.
///
/// If the option is `None`, it means the item is to be ignored (example: it
/// is a `use` item).
///
/// Rk.: this function is only used by [register], and written in this context.
pub fn hir_item_to_name(tcx: TyCtxt, item: &Item) -> Option<HirItemName> {
    let def_id = item.def_id.to_def_id();

    // TODO: calling different functions to retrieve the name is not very
    // satisfying below
    match &item.kind {
        ItemKind::OpaqueTy(_) => unimplemented!(),
        ItemKind::Union(_, _) => unimplemented!(),
        ItemKind::ExternCrate(_) => {
            // We ignore this -
            // TODO: investigate when extern crates appear, and why
            Option::None
        }
        ItemKind::Use(_, _) => Option::None,
        ItemKind::TyAlias(_, _) => {
            // We ignore the type aliases - it seems they are inlined
            Option::None
        }
        ItemKind::Enum(_, _)
        | ItemKind::Struct(_, _)
        | ItemKind::Fn(_, _, _)
        | ItemKind::Impl(_)
        | ItemKind::Mod(_)
        | ItemKind::Const(_, _)
        | ItemKind::Macro(_) => Option::Some(item_def_id_to_name(tcx, def_id)),
        _ => {
            unimplemented!("{:?}", item.kind);
        }
    }
}
