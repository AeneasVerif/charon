//! Analysis of type defintions and function signatures to compute the
//! hierarchy between regions.
#![allow(dead_code)]

use crate::cfim_ast::FunDefs;
use crate::common::*;
use crate::graphs::*;
use crate::im_ast::{FunDefId, FunSig};
use crate::types::*;
use macros::generate_index_type;
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use petgraph::Direction;
use serde::Serialize;

generate_index_type!(RegionGroupId);

/// An edge from r1 to r2 means:
/// r1 : r2 (i.e.: r1 lasts longer than r2)
type LifetimeConstraints = DiGraphMap<Region<RegionVarId::Id>, ()>;

/// A group of regions.
///
/// Is used to group regions with the same lifetime together, and express
/// the lifetime hierarchy between different groups of regions.
#[derive(Debug, Clone, Serialize)]
pub struct RegionGroup {
    /// The region group identifier
    pub id: RegionGroupId::Id,
    /// The regions included in this group
    pub regions: Vec<RegionVarId::Id>,
    /// The parent region groups
    pub parents: Vec<RegionGroupId::Id>,
}

pub type RegionGroups = RegionGroupId::Vector<RegionGroup>;

fn add_opt_region_constraints(
    constraints: &mut LifetimeConstraints,
    region: Region<RegionVarId::Id>,
    opt_parent: &Option<Region<RegionVarId::Id>>,
) {
    if !constraints.contains_node(region) {
        constraints.add_node(region);
    }

    match opt_parent {
        None => (),
        Some(parent) => {
            let parent = *parent;
            if !constraints.contains_node(parent) {
                constraints.add_node(parent);
            }
            constraints.add_edge(region, parent, ());
        }
    }

    // Also constrain with regards to static:
    constraints.add_edge(Region::Static, region, ());
}

/// The computation of a regions hierarchy is done in two steps:
/// - first we visit the type definition/function signature to register the
///   constraints between the different regions
/// - then we compute the hierarchy from those accumulated constraints
/// This function performs the second step.
fn compute_regions_hierarchy_from_constraints(
    mut constraints: SCCs<Region<RegionVarId::Id>>,
) -> RegionGroups {
    // The last SCC **MUST** contain the static region.
    // For now, we don't handle cases where regions different from 'static
    // can live as long as 'static, so we check that the last scc is the
    // {static} singleton.
    // TODO: general support for 'static
    assert!(constraints.sccs.len() >= 1);
    assert!(constraints.sccs.last().unwrap() == &vec![Region::Static]);

    // Pop the last SCC (which is {'static}).
    let _ = constraints.sccs.pop();
    let _ = constraints.scc_deps.pop();

    // Compute the hierarchy
    let mut groups = RegionGroups::new();
    for (i, scc) in constraints.sccs.into_iter().enumerate() {
        // Compute the id
        let id = RegionGroupId::Id::new(i);

        // Retrieve the set of regions in the group
        let regions: Vec<RegionVarId::Id> = scc.into_iter().map(|r| *r.as_var()).collect();

        // Compute the set of parent region groups
        let parents: Vec<RegionGroupId::Id> = constraints
            .scc_deps
            .get(i)
            .unwrap()
            .iter()
            .map(|j| RegionGroupId::Id::new(*j))
            .collect();

        // Push the group
        groups.push_back(RegionGroup {
            id,
            regions,
            parents,
        });
    }

    // Return
    groups
}

/*
/// Compute the region hierarchy (the order between the region's lifetimes)
/// for a (group of mutually recursive) type definitions.
/// Note that [TypeDef] already contains a regions hierarchy: when translating
/// function signatures, we first translate the signature without this hierarchy,
/// then compute this hierarchy and add it to the signature information.
pub fn compute_regions_group_hierarchy_for_type_decl(
    types: &TypeDefs,
    decl :
    def: &TypeDef,
) -> RegionsGroup {

}*/

/// Compute the constraints between the different regions of a type (which
/// region lasts longer than which other region, etc.).
/// Note that the region hierarchies should already have been computed for all
/// the types.
fn compute_region_constraints_for_ty(
    constraints: &mut LifetimeConstraints,
    parent_region: Option<Region<RegionVarId::Id>>,
    ty: &RTy,
) {
    match ty {
        Ty::Adt(_type_id, regions, types) => {
            // TODO: check the type's lifetime constraints (written in the type
            // declaration) if the type is a user-defined ADT

            // Introduce constraints for all the regions
            for r in regions {
                add_opt_region_constraints(constraints, *r, &parent_region);
            }

            // Explore the types given as parameters
            for fty in types {
                compute_region_constraints_for_ty(constraints, parent_region, fty);
            }
        }
        Ty::TypeVar(_) | Ty::Bool | Ty::Char | Ty::Never | Ty::Integer(_) | Ty::Str => {
            // Nothing to do
        }
        Ty::Array(_aty) => {
            unimplemented!();
        }
        Ty::Slice(_sty) => {
            unimplemented!();
        }
        Ty::Ref(region, ref_ty, _mutability) => {
            // Add the constraint for the region in the reference
            add_opt_region_constraints(constraints, *region, &parent_region);

            // Update the parent region, then continue exploring
            compute_region_constraints_for_ty(constraints, Some(*region), ref_ty);
        }
    }
}

/// Compute the constraints between the different regions of a function
/// signature (which region lasts longer than which other region, etc.).
/// This is used to compute the order (in given by the region lifetime's)
/// between the regions.
fn compute_region_constraints_for_sig(sig: &FunSig) -> SCCs<Region<RegionVarId::Id>> {
    let mut constraints_graph = LifetimeConstraints::new();
    constraints_graph.add_node(Region::Static);

    for input_ty in &sig.inputs {
        compute_region_constraints_for_ty(&mut constraints_graph, None, input_ty);
    }
    compute_region_constraints_for_ty(&mut constraints_graph, None, &sig.output);

    // Apply Tarjan's algorithms to group the regions and the borrows which have
    // the same lifetime. We then reorder those group of regions to be as close
    // as possible to the original order.
    let region_sccs = tarjan_scc(&constraints_graph);

    // Reorder the SCCs
    let get_region_parents = &|r: Region<RegionVarId::Id>| {
        constraints_graph
            .neighbors_directed(r, Direction::Outgoing)
            .collect()
    };

    // Option::iter is a trick to easily append a single region to the var regions
    // Maybe there is a better way.
    let all_var_regions = sig.region_params.iter_indices().map(|id| Region::Var(id));
    let all_rids: Vec<Region<RegionVarId::Id>> = all_var_regions
        .chain(Some(Region::Static).into_iter())
        .collect();
    let sccs = reorder_sccs(get_region_parents, &all_rids, &region_sccs);

    // Debugging
    trace!(
        "{}",
        vec_to_string(
            &|scc: &Vec<Region<RegionVarId::Id>>| {
                let ids: Vec<String> = scc.iter().map(|r| r.to_string()).collect();
                format!("[{}]", ids.join(", "))
            },
            &sccs.sccs
        )
    );

    sccs
}

/// Compute the region hierarchy (the order between the region's lifetimes)
/// for a function signature.
/// Note that [FunSig] already contains a regions hierarchy: when translating
/// function signatures, we first translate the signature without this hierarchy,
/// then compute this hierarchy and add it to the signature information.
pub fn compute_region_groups_hierarchy_for_sig(sig: &FunSig) -> RegionGroups {
    // Compute the constraints between the regions and group them accordingly
    let sccs = compute_region_constraints_for_sig(sig);

    // Compute the regions hierarchy
    compute_regions_hierarchy_from_constraints(sccs)
}

/// Compute the region hierarchy (the order between the region's lifetimes) for
/// a set of function definitions.
pub fn compute_regions_hierarchies(defs: &FunDefs) -> FunDefId::Vector<RegionGroups> {
    use std::iter::FromIterator;
    FunDefId::Vector::from_iter(
        defs.iter()
            .map(|def| compute_region_groups_hierarchy_for_sig(&def.signature)),
    )
}
