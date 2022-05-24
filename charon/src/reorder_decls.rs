use crate::common::*;
use crate::graphs::*;
use crate::register::RegisteredDeclarations;
use macros::{VariantIndexArity, VariantName};
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use rustc_hir::def_id::DefId;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::collections::HashSet;
use std::fmt::{Debug, Display, Error, Formatter};
use std::vec::Vec;

/// A (group of) top-level declaration(s), properly reordered.
/// "G" stands for "generic"
#[derive(Debug, VariantIndexArity, VariantName)]
pub enum GDeclarationGroup<Id: Copy> {
    /// A non-recursive declaration
    NonRec(Id),
    /// A (group of mutually) recursive declaration(s)
    Rec(Vec<Id>),
}

/// A (group of) top-level declaration(s), properly reordered.
#[derive(Debug, VariantIndexArity, VariantName)]
pub enum DeclarationGroup<TypeId: Copy, FunId: Copy, ConstId: Copy> {
    /// A type declaration group
    Type(GDeclarationGroup<TypeId>),
    /// A function declaration group
    Fun(GDeclarationGroup<FunId>),
    /// A constant declaration group
    Const(GDeclarationGroup<ConstId>),
}

/// The top-level declarations in a module
pub struct DeclarationsGroups<TypeId: Copy, FunId: Copy, ConstId: Copy> {
    /// The properly grouped and ordered declarations
    pub decls: Vec<DeclarationGroup<TypeId, FunId, ConstId>>,
    /// All the type ids
    pub type_ids: Vec<TypeId>,
    /// All the function ids
    pub fun_ids: Vec<FunId>,
    /// All the constant ids
    pub const_ids: Vec<ConstId>,
    /// All the opaque/external type ids
    pub external_type_ids: HashSet<TypeId>,
    /// All the opaque/external fun ids
    pub external_fun_ids: HashSet<FunId>,
    /// All the opaque/external const ids
    pub external_const_ids: HashSet<ConstId>,
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<Id: Copy + Debug> Display for GDeclarationGroup<Id> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            GDeclarationGroup::NonRec(id) => write!(f, "non-rec: {:?}", id),
            GDeclarationGroup::Rec(ids) => write!(
                f,
                "rec: {}",
                vec_to_string(&|id| format!("    {:?}", id).to_string(), ids)
            ),
        }
    }
}

/// This is a bit annoying: because [DefId] and [Vec] doe't implement the
/// [Serialize] trait, we can't automatically derive the serializing trait...
impl<Id: Copy + Serialize> Serialize for GDeclarationGroup<Id> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "GDeclarationGroup";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        assert!(variant_arity > 0);
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            GDeclarationGroup::NonRec(id) => {
                vs.serialize_field(id)?;
            }
            GDeclarationGroup::Rec(ids) => {
                let ids = VecSerializer::new(ids);
                vs.serialize_field(&ids)?;
            }
        }
        vs.end()
    }
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<TypeId: Copy + Debug, FunId: Copy + Debug, ConstId: Copy + Debug> Display
    for DeclarationGroup<TypeId, FunId, ConstId>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            DeclarationGroup::Type(decl) => write!(f, "{{ Type(s): {} }}", decl),
            DeclarationGroup::Fun(decl) => write!(f, "{{ Fun(s): {} }}", decl),
            DeclarationGroup::Const(decl) => write!(f, "{{ Const(s): {} }}", decl),
        }
    }
}

/// This is a bit annoying: because [DefId] and [Vec] doe't implement the
/// [Serialize] trait, we can't automatically derive the serializing trait...
impl<TypeId: Copy + Serialize, FunId: Copy + Serialize, ConstId: Copy + Serialize> Serialize
    for DeclarationGroup<TypeId, FunId, ConstId>
{
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "DeclarationGroup";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        assert!(variant_arity > 0);
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            DeclarationGroup::Type(decl) => {
                vs.serialize_field(decl)?;
            }
            DeclarationGroup::Fun(decl) => {
                vs.serialize_field(decl)?;
            }
            DeclarationGroup::Const(decl) => {
                vs.serialize_field(decl)?;
            }
        }
        vs.end()
    }
}

impl<TypeId: Copy, FunId: Copy, ConstId: Copy> DeclarationsGroups<TypeId, FunId, ConstId> {
    pub fn new() -> DeclarationsGroups<TypeId, FunId, ConstId> {
        DeclarationsGroups {
            decls: vec![],
            type_ids: vec![],
            fun_ids: vec![],
            const_ids: vec![],
            external_type_ids: HashSet::new(),
            external_fun_ids: HashSet::new(),
            external_const_ids: HashSet::new(),
        }
    }

    fn push(&mut self, decl: DeclarationGroup<TypeId, FunId, ConstId>) {
        match &decl {
            DeclarationGroup::Type(GDeclarationGroup::NonRec(id)) => {
                self.type_ids.push(*id);
            }
            DeclarationGroup::Type(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.type_ids.push(*id);
                }
            }
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)) => {
                self.fun_ids.push(*id);
            }
            DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.fun_ids.push(*id);
                }
            }
            DeclarationGroup::Const(GDeclarationGroup::NonRec(id)) => {
                self.const_ids.push(*id);
            }
            DeclarationGroup::Const(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.const_ids.push(*id);
                }
            }
        }
        self.decls.push(decl);
    }
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<TypeId: Copy + Debug, FunId: Copy + Debug, ConstId: Copy + Debug> Display
    for DeclarationsGroups<TypeId, FunId, ConstId>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        write!(
            f,
            "{}",
            vec_to_string(
                &|d: &DeclarationGroup<TypeId, FunId, ConstId>| d.to_string(),
                &self.decls,
            )
        )
    }
}

impl<'a, TypeId: Copy, FunId: Copy, ConstId: Copy> std::iter::IntoIterator
    for &'a DeclarationsGroups<TypeId, FunId, ConstId>
{
    type Item = &'a DeclarationGroup<TypeId, FunId, ConstId>;
    type IntoIter = std::slice::Iter<'a, DeclarationGroup<TypeId, FunId, ConstId>>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.decls.iter()
    }
}

#[derive(PartialEq, Eq)]
enum DefIdKind {
    Type,
    Fun,
    Const,
}

// Less efficient than a lookup on the needed type, but performs a sanity check.
fn get_def_id_kind(decls: &RegisteredDeclarations, def_id: &DefId) -> DefIdKind {
    if decls.types.contains_key(def_id) {
        DefIdKind::Type
    } else if decls.funs.contains_key(def_id) {
        DefIdKind::Fun
    } else if decls.consts.contains_key(def_id) {
        DefIdKind::Const
    } else {
        panic!("unknown id {:?}", def_id);
    }
}

pub fn reorder_declarations(
    decls: &RegisteredDeclarations,
) -> Result<DeclarationsGroups<DefId, DefId, DefId>> {
    trace!();

    // Step 1: Start by building the graph
    let mut graph = DiGraphMap::<DefId, ()>::new();

    // Add the nodes - note that we are using both local and external def ids.
    for d in decls.decls.iter() {
        graph.add_node(*d);
    }

    // Add the edges.
    // Note that some of the dependencies might be foreign dependencies (i.e.:
    // not defined in the local crate).
    // Types -> types
    decls.types.iter().for_each(|(id, d)| {
        d.deps.iter().for_each(|dep_id| {
            let _ = graph.add_edge(*id, *dep_id, ());
        })
    });
    // Functions
    decls.funs.iter().for_each(|(id, d)| {
        // Functions -> types
        d.deps_tys.iter().for_each(|dep_id| {
            let _ = graph.add_edge(*id, *dep_id, ());
        });
        // Functions -> functions
        d.deps_funs.iter().for_each(|dep_id| {
            let _ = graph.add_edge(*id, *dep_id, ());
        });
        // Functions -> constants
        d.deps_consts.iter().for_each(|dep_id| {
            let _ = graph.add_edge(*id, *dep_id, ());
        });
    });
    // Constants
    decls.funs.iter().for_each(|(id, d)| {
        // Constants -> types
        d.deps_tys.iter().for_each(|dep_id| {
            let _ = graph.add_edge(*id, *dep_id, ());
        });
        // Constants -> functions
        d.deps_funs.iter().for_each(|dep_id| {
            let _ = graph.add_edge(*id, *dep_id, ());
        });
        // Constants -> constants
        d.deps_consts.iter().for_each(|dep_id| {
            let _ = graph.add_edge(*id, *dep_id, ());
        });
    });

    trace!("Graph: {:?}", graph);

    // Step 2: Apply Tarjan's SCC (Strongly Connected Components) algorithm
    let sccs = tarjan_scc(&graph);

    // Step 3: Reorder the declarations in an order as close as possible to the one
    // given by the user. To be more precise, if we don't need to move
    // definitions, the order in which we generate the declarations should
    // be the same as the one in which the user wrote them.
    let get_id_dependencies: &dyn Fn(DefId) -> Vec<DefId> = &|id| {
        match get_def_id_kind(decls, &id) {
            DefIdKind::Type => {
                // Retrieve the type dependencies, and filter the foreign ids
                decls
                    .types
                    .get(&id)
                    .unwrap()
                    .deps
                    .iter()
                    .map(|id| *id)
                    .collect()
            }
            DefIdKind::Fun => {
                let decl = &decls.funs.get(&id).unwrap();
                // We need to chain the type and the function dependencies, and
                // filter the foreign ids
                decl.deps_tys
                    .iter()
                    .chain(decl.deps_funs.iter())
                    .chain(decl.deps_consts.iter())
                    .map(|id| *id)
                    .collect()
            }
            DefIdKind::Const => {
                let decl = &decls.consts.get(&id).unwrap();
                // We need to chain the type and the constant dependencies, and
                // filter the foreign ids
                decl.deps_tys
                    .iter()
                    .chain(decl.deps_funs.iter())
                    .chain(decl.deps_consts.iter())
                    .map(|id| *id)
                    .collect()
            }
        }
    };
    let SCCs {
        sccs: reordered_sccs,
        scc_deps: _,
    } = reorder_sccs::<DefId>(
        get_id_dependencies,
        &decls.decls.iter().map(|id| *id).collect(),
        &sccs,
    );

    // Finally, generate the list of declarations
    let mut reordered_decls = DeclarationsGroups::new();

    // Iterate over the SCC ids in the proper order
    for scc in reordered_sccs.iter() {
        // Retrieve the SCC
        assert!(scc.len() > 0);

        // Sanity check: make sure an SCC is made of type declarations only,
        // or of function declarations only.
        // Note that the length of an SCC should be at least 1.
        let mut it = scc.iter();
        let id0 = it.next().unwrap();
        let def_kind = get_def_id_kind(decls, &id0);

        for id in it {
            match def_kind {
                DefIdKind::Type => assert!(decls.types.contains_key(id)),
                DefIdKind::Fun => assert!(decls.funs.contains_key(id)),
                DefIdKind::Const => assert!(decls.consts.contains_key(id)),
            }
        }

        // If an SCC has length one, the declaration may be simply recursive:
        // we determine whether it is the case by checking if the def id is in
        // its own set of dependencies.
        let is_simply_recursive;
        if scc.len() == 1 {
            let deps = match def_kind {
                DefIdKind::Type => &decls.types.get(&id0).unwrap().deps,
                DefIdKind::Fun => &decls.funs.get(&id0).unwrap().deps_funs,
                DefIdKind::Const => &decls.consts.get(&id0).unwrap().deps_consts,
            };
            is_simply_recursive = deps.contains(&id0);
        } else {
            is_simply_recursive = false;
        }

        // Add the declaration.
        // Note that we clone the vectors: it is not optimal, but they should
        // be pretty small.
        let wrap_group = |x| match def_kind {
            DefIdKind::Type => DeclarationGroup::Type(x),
            DefIdKind::Fun => DeclarationGroup::Fun(x),
            DefIdKind::Const => DeclarationGroup::Const(x),
        };
        if scc.len() == 1 && !is_simply_recursive {
            reordered_decls.push(wrap_group(GDeclarationGroup::NonRec(*id0)));
        } else {
            reordered_decls.push(wrap_group(GDeclarationGroup::Rec(scc.clone())));
        }
    }

    trace!("{}", reordered_decls.to_string());

    // We list the external definitions (opaque local, and non-local)
    for id in decls.decls.iter() {
        match get_def_id_kind(decls, id) {
            DefIdKind::Type => {
                if !id.is_local() || decls.opaque_types.contains(id) {
                    reordered_decls.external_type_ids.insert(*id);
                }
            }
            DefIdKind::Fun => {
                if !id.is_local() || decls.opaque_funs.contains(id) {
                    reordered_decls.external_fun_ids.insert(*id);
                }
            }
            DefIdKind::Const => {
                if !id.is_local() || decls.opaque_consts.contains(id) {
                    reordered_decls.external_const_ids.insert(*id);
                }
            }
        }
    }

    // TODO: check that the mutually recursive groups don't mix opaque and
    // transparent definitions (this is for sanity: this really *shouldn't*
    // happen).

    return Ok(reordered_decls);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_reorder_sccs1() {
        let sccs = vec![vec![0], vec![1, 2], vec![3, 4, 5]];
        let ids = vec![0, 1, 2, 3, 4, 5];

        let get_deps = &|x| match x {
            0 => vec![3],
            1 => vec![0, 3],
            _ => vec![],
        };
        let reordered = crate::reorder_decls::reorder_sccs(get_deps, &ids, &sccs);

        assert!(reordered.sccs == vec![vec![3, 4, 5], vec![0], vec![1, 2],]);
        assert!(reordered.scc_deps[0] == im::OrdSet::from(vec![]));
        assert!(reordered.scc_deps[1] == im::OrdSet::from(vec![0]));
        assert!(reordered.scc_deps[2] == im::OrdSet::from(vec![0, 1]));
    }
}
