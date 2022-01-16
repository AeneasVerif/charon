use crate::cfim_ast as cfim;
use crate::im_ast as ast;
use crate::register::RegisteredDeclarations;
use crate::rust_to_local_ids::*;
use rustc_hir::def_id::DefId;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

fn statement_diverges(divergent: &HashMap<ast::FunDefId::Id, bool>, st: &cfim::Statement) -> bool {
    match st {
        cfim::Statement::Assign(_, _)
        | cfim::Statement::FakeRead(_)
        | cfim::Statement::SetDiscriminant(_, _)
        | cfim::Statement::Drop(_)
        | cfim::Statement::Assert(_)
        | cfim::Statement::Panic
        | cfim::Statement::Return
        | cfim::Statement::Break(_)
        | cfim::Statement::Continue(_)
        | cfim::Statement::Nop => false,
        cfim::Statement::Call(call) => match &call.func {
            ast::FunId::Local(id) => *divergent.get(id).unwrap(),
            ast::FunId::Assumed(id) => match id {
                ast::AssumedFunId::BoxNew
                | ast::AssumedFunId::BoxDeref
                | ast::AssumedFunId::BoxDerefMut
                | ast::AssumedFunId::BoxFree => false,
            },
        },
        cfim::Statement::Sequence(st1, st2) => {
            statement_diverges(divergent, &st1) || statement_diverges(divergent, &st2)
        }
        cfim::Statement::Switch(_, tgts) => {
            let tgts = tgts.get_targets();
            tgts.iter().any(|st| statement_diverges(divergent, st))
        }
        cfim::Statement::Loop(_) => true,
    }
}

fn fun_diverges(divergent: &HashMap<ast::FunDefId::Id, bool>, def: &cfim::FunDef) -> bool {
    statement_diverges(divergent, &def.body)
}

/// Compute which functions can loop.
/// This is a rather crude analysis, which simply checks if a function is
/// recursive or contains a loop, or transitively calls such a function.
/// In the future, we may perform more precise analyses later to check if a
/// recursive function or a function containing a loop is actually structurally
/// terminating.
pub fn compute_divergent_functions(
    decls: &OrderedDecls,
    defs: &cfim::FunDefs,
) -> HashSet<ast::FunDefId::Id> {
    // For sanity, we use a map rather than a set, so that we can check
    // that we have indeed computed the divergence for the previous
    // declarations.
    let mut divergent_map: HashMap<ast::FunDefId::Id, bool> = HashMap::new();

    // The declarations in decls have been reordered so that the dependencies
    // of every group of declarations is either in the group itself (in case
    // of recursive functions), in declarations from external crates, or
    // in declarations which happen before in the list of declarations.
    for decl in &decls.decls {
        match decl {
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)) => {
                // Non-recursive function: we have to check the body
                divergent_map.insert(*id, fun_diverges(&divergent_map, defs.get(*id).unwrap()));
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

    // Convert the map to a set
    let mut divergent_set: HashSet<ast::FunDefId::Id> = HashSet::from_iter(
        divergent_map
            .iter()
            .filter(|(id, div)| **div)
            .map(|(id, _)| *id),
    );
    divergent_set
}
