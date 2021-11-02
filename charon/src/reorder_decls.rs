use crate::common::*;
use crate::graphs::*;
use crate::register::RegisteredDeclarations;
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use rustc_hir::def_id::DefId;
use std::vec::Vec;

/// A (group of) top-level declaration(s), properly reordered.
/// TODO: rename to DeclarationGroup
#[derive(Debug)]
pub enum Declaration {
    /// A non-recursive type declaration.
    Type(DefId),
    /// A non-recursive function declaration
    Fun(DefId),
    /// A group of mutually recursive function declarations. If only one
    /// declaration, it means it is a simply recursive one.
    RecTypes(Vec<DefId>),
    /// A group of mutually recursive function declarations. If only one
    /// declaration, it means it is a simply recursive one.
    RecFuns(Vec<DefId>),
}

impl Declaration {
    fn to_string(decl: &Declaration) -> String {
        match decl {
            Declaration::Type(id) => format!("{{ Type: {:?} }}", id).to_string(),
            Declaration::Fun(id) => format!("{{ Fun: {:?} }}", id).to_string(),
            Declaration::RecTypes(ids) => format!(
                "{{ RecTypes: {} }}",
                vec_to_string(&|id| format!("    {:?}", id).to_string(), ids)
            )
            .to_string(),
            Declaration::RecFuns(ids) => format!(
                "{{ RecFuns: {} }}",
                vec_to_string(&|id| format!("    {:?}", id).to_string(), ids)
            )
            .to_string(),
        }
    }
}

impl ToString for Declaration {
    fn to_string(&self) -> String {
        Declaration::to_string(self)
    }
}

pub struct Declarations {
    /// The properly grouped and ordered def ids
    pub decls: Vec<Declaration>,
    /// All the type ids
    pub type_ids: Vec<DefId>,
    /// All the fun ids
    pub fun_ids: Vec<DefId>,
}

impl Declarations {
    pub fn new() -> Declarations {
        Declarations {
            decls: vec![],
            type_ids: vec![],
            fun_ids: vec![],
        }
    }

    fn to_string(decls: &Declarations) -> String {
        vec_to_string(&|d: &Declaration| d.to_string(), &decls.decls)
    }

    fn push(&mut self, decl: Declaration) {
        match &decl {
            Declaration::Type(def_id) => {
                self.type_ids.push(*def_id);
            }
            Declaration::RecTypes(def_ids) => {
                for def_id in def_ids {
                    self.type_ids.push(*def_id);
                }
            }
            Declaration::Fun(def_id) => {
                self.fun_ids.push(*def_id);
            }
            Declaration::RecFuns(def_ids) => {
                for def_id in def_ids {
                    self.fun_ids.push(*def_id);
                }
            }
        }
        self.decls.push(decl);
    }
}

impl ToString for Declarations {
    fn to_string(&self) -> String {
        Declarations::to_string(self)
    }
}

impl<'a> std::iter::IntoIterator for &'a Declarations {
    type Item = &'a Declaration;
    type IntoIter = std::slice::Iter<'a, Declaration>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.decls.iter()
    }
}

fn def_id_is_type(decls: &RegisteredDeclarations, def_id: &DefId) -> bool {
    // This is not efficient, but it is good to perform a sanity check
    if decls.types.get(def_id).is_some() {
        return true;
    } else {
        assert!(decls.funs.get(def_id).is_some());
        return false;
    }
}

pub fn reorder_declarations(decls: &RegisteredDeclarations) -> Result<Declarations> {
    trace!();

    // Step 1: Start by building a graph
    let mut graph = DiGraphMap::<DefId, ()>::new();

    // Add the nodes - note that decls.decls only contains local def ids
    // (but the dependency vectors might contain foreign def ids).
    for d in decls.decls.iter() {
        assert!(d.is_local());
        graph.add_node(*d);
    }

    // Add the edges.
    // Note that some of the dependencies might be foreign depedencies (i.e.:
    // not defined in the local crate). We ignore those.
    // Types -> types
    decls.types.iter().for_each(|(id, d)| {
        d.deps.iter().for_each(|dep_id| {
            if dep_id.is_local() {
                let _ = graph.add_edge(*id, *dep_id, ());
                ()
            }
        })
    });
    // Functions -> types
    decls.funs.iter().for_each(|(id, d)| {
        // Functions -> types
        d.deps_tys.iter().for_each(|dep_id| {
            if dep_id.is_local() {
                let _ = graph.add_edge(*id, *dep_id, ());
                ()
            }
        });
        // Functions -> functions
        d.deps_funs.iter().for_each(|dep_id| {
            if dep_id.is_local() {
                let _ = graph.add_edge(*id, *dep_id, ());
                ()
            }
        })
    });

    // Step 2: Apply Tarjan's SCC (Strongly Connected Components) algorithm
    let sccs = tarjan_scc(&graph);

    // Step 3: Reorder the declarations in an order as close as possible to the one
    // given by the user. To be more precise, if we don't need to move
    // definitions, the order in which we generate the declarations should
    // be the same as the one in which the user wrote them.
    let get_id_dependencies: &dyn Fn(DefId) -> Vec<DefId> = &|id| {
        if def_id_is_type(decls, &id) {
            // Retrieve the type dependencies, and filter the foreign ids
            decls
                .types
                .get(&id)
                .unwrap()
                .deps
                .iter()
                .map(|id| *id)
                .filter(|id| id.is_local())
                .collect()
        } else {
            let decl = &decls.funs.get(&id).unwrap();
            // We need to chain the type and the function dependencies, and
            // filter the foreign ids
            decl.deps_tys
                .iter()
                .chain(decl.deps_funs.iter())
                .map(|id| *id)
                .filter(|id| id.is_local())
                .collect()
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
    let mut reordered_decls = Declarations::new();

    // Iterate over the SCC ids in the proper order
    for scc in reordered_sccs.iter() {
        // Retrieve the SCC
        assert!(scc.len() > 0);

        // Sanity check: make sure an SCC is made of type declarations only,
        // or of function declarations only.
        // Note that the length of an SCC should be at least 1.
        let mut it = scc.iter();
        let id0 = it.next().unwrap();
        let is_type = def_id_is_type(decls, &id0);

        for id in it {
            assert!(is_type == decls.types.get(id).is_some());
        }

        // If an SCC has length one, the declaration may be simply recursive:
        // we determine whether it is the case by checking if the def id is in
        // its own set of dependencies.
        let is_simply_recursive;
        if scc.len() == 1 {
            let deps = if is_type {
                &decls.types.get(&id0).unwrap().deps
            } else {
                &decls.funs.get(&id0).unwrap().deps_funs
            };

            is_simply_recursive = deps.contains(&id0);
        } else {
            is_simply_recursive = false;
        }

        // Add the declaration.
        // Note that we clone the vectors: it is not optimal, but they should
        // be pretty small.
        if is_type {
            if scc.len() == 1 && !is_simply_recursive {
                reordered_decls.push(Declaration::Type(*id0));
            } else {
                reordered_decls.push(Declaration::RecTypes(scc.clone()));
            }
        } else {
            if scc.len() == 1 && !is_simply_recursive {
                reordered_decls.push(Declaration::Fun(*id0));
            } else {
                reordered_decls.push(Declaration::RecFuns(scc.clone()));
            }
        }
    }

    trace!("{}", reordered_decls.to_string());

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
