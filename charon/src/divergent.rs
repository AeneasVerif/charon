use crate::register::RegisteredDeclarations;
use crate::reorder_decls;
use crate::reorder_decls::{DeclarationGroup, GDeclarationGroup};
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

/// Compute which functions can loop.
/// This is a rather crude analysis, which simply checks if a function is
/// recursive or transitively calls a recursive function.
/// In the future, we may perform more precise analyses later to check if a
/// recursive function or a function containing a loop is actually not
/// terminating by construction.
pub fn compute_divergent_functions(
    deps: &RegisteredDeclarations,
    decls: &reorder_decls::DeclarationsGroups<DefId, DefId>,
) -> HashMap<DefId, bool> {
    let mut divergent_map: HashMap<DefId, bool> = HashMap::new();

    // The declarations in decls have been reordered so that the dependencies
    // of every group of declarations is either in the group itself, in
    // declarations from external crates, or in declarations which happen
    // before in the list of declarations.
    for decl in &decls.decls {
        match decl {
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)) => {
                // We have to explore the dependencies to see if some of them
                // can loop.
                let deps = deps.funs.get(&id).unwrap();

                let mut can_diverge = false;
                for dep_id in &deps.deps_funs {
                    // All the non-local functions are total for now.
                    // The reason is that we accept only a limited set of
                    // functions, from the standard library for instance,
                    // which are total. If we find functions oustide of this
                    // set, the program is rejected.
                    if dep_id.is_local() {
                        if *divergent_map.get(&dep_id).unwrap() {
                            can_diverge = true;
                            break;
                        }
                    }
                }

                divergent_map.insert(*id, can_diverge);
            }
            DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)) => {
                // Trivial case: recursive declarations can diverge
                for id in ids {
                    divergent_map.insert(*id, true);
                }
            }
            DeclarationGroup::Type(_) => {
                // Ignore the type declarations
                continue;
            }
        }
    }

    divergent_map
}
