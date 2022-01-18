//! Analysis of type defintions and function signatures to compute the
//! hierarchy between regions.
#![allow(dead_code)]

use crate::cfim_ast::FunDefs;
use crate::common::*;
use crate::formatter::Formatter;
use crate::graphs::*;
use crate::im_ast::{FunDefId, FunSig};
use crate::rust_to_local_ids::TypeDeclarationGroup;
use crate::types as ty;
use crate::types::*;
use macros::generate_index_type;
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use petgraph::Direction;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

generate_index_type!(RegionGroupId);

pub fn region_group_id_to_pretty_string(rid: RegionGroupId::Id) -> String {
    format!("rg@{}", rid).to_string()
}

#[derive(Copy, Clone)]
pub struct LifetimeConstraint {
    region: Region<RegionVarId::Id>,
    parent: Region<RegionVarId::Id>,
}

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

/// Compute the region strongly connected components from a constraints graph.
fn compute_sccs_from_lifetime_constraints(
    constraints_graph: &LifetimeConstraints,
    region_params: &RegionVarId::Vector<RegionVar>,
) -> SCCs<Region<RegionVarId::Id>> {
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
    let all_var_regions = region_params.iter_indices().map(|id| Region::Var(id));
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

/// See [TypesConstraintsMap]
pub type TypeVarsConstraintsMap = HashMap<TypeVarId::Id, HashSet<Region<RegionVarId::Id>>>;

/// This map gives, for every type parameter of every type definition, the set
/// of regions under which the type parameter appears.
/// For instance, for the following type definition:
/// ```
/// struct S<'a, 'b, T1, T2> {
///   x : T1,
///   y : &'a mut &'b mut T2,
/// }
/// ```
///
/// We would have:
/// ```
/// T1 -> {}
/// T2 -> {'a, 'b}
/// ```
pub type TypesConstraintsMap = HashMap<TypeDefId::Id, TypeVarsConstraintsMap>;

fn add_region_constraints(
    updated: &mut bool,
    acc_constraints: &mut LifetimeConstraints,
    region: Region<RegionVarId::Id>,
    parent_regions: &im::HashSet<Region<RegionVarId::Id>>,
) {
    // Check that the region is indeed in the nodes
    if !acc_constraints.contains_node(region) {
        *updated = true;
        acc_constraints.add_node(region);
    }

    for parent in parent_regions.iter() {
        let parent = *parent;
        if !acc_constraints.contains_node(parent) {
            *updated = true;
            acc_constraints.add_node(parent);
        }
        if !acc_constraints.contains_edge(region, parent) {
            *updated = true;
            acc_constraints.add_edge(region, parent, ());
        }
    }

    // Also constrain with regards to static:
    if !acc_constraints.contains_edge(Region::Static, region) {
        *updated = true;
        acc_constraints.add_edge(Region::Static, region, ());
    }
}

/// TODO: detailed explanations
fn compute_full_regions_constraints_for_ty(
    updated: &mut bool,
    constraints_map: &TypesConstraintsMap,
    acc_constraints: &mut LifetimeConstraints,
    type_vars_constraints: &mut Option<TypeVarsConstraintsMap>, // TODO: rename
    parent_regions: im::HashSet<Region<RegionVarId::Id>>,
    ty: &RTy,
) {
    match ty {
        Ty::Adt(type_id, regions, types) => {
            // Introduce constraints for all the regions given as parameters
            for r in regions {
                add_region_constraints(updated, acc_constraints, *r, &parent_regions);
            }

            // Compute the map from region param id to region instantation, for
            // this ADT instantiation
            let region_inst: RegionVarId::Vector<Region<RegionVarId::Id>> =
                RegionVarId::Vector::from_iter(regions.iter().map(|r| *r));

            // Lookup the constraints for this type definition
            match type_id {
                TypeId::Adt(type_def_id) => {
                    // Lookup the type parameter constraints for this ADT
                    let type_def_constraints = constraints_map.get(type_def_id).unwrap();

                    // Explore the types given as parameters
                    let types: TypeVarId::Vector<&RTy> = TypeVarId::Vector::from_iter(types.iter());
                    for (type_param_id, fty) in types.iter_indexed_values() {
                        // Retrieve the parent regions for this type param
                        let type_param_constraints =
                            type_def_constraints.get(&type_param_id).unwrap();

                        // Instantiate the parent regions constraints
                        let mut parent_regions = parent_regions.clone();
                        for r in type_param_constraints {
                            let region = match r {
                                Region::Static => Region::Static,
                                Region::Var(rid) => *region_inst.get(*rid).unwrap(),
                            };
                            parent_regions.insert(region);
                        }

                        // Explore the type parameter
                        compute_full_regions_constraints_for_ty(
                            updated,
                            constraints_map,
                            acc_constraints,
                            type_vars_constraints,
                            parent_regions.clone(),
                            fty,
                        );
                    }
                }
                TypeId::Tuple | TypeId::Assumed(AssumedTy::Box) => {
                    // Explore the types given as parameters
                    for fty in types {
                        compute_full_regions_constraints_for_ty(
                            updated,
                            constraints_map,
                            acc_constraints,
                            type_vars_constraints,
                            parent_regions.clone(),
                            fty,
                        );
                    }
                }
            }
        }
        Ty::Bool | Ty::Char | Ty::Never | Ty::Integer(_) | Ty::Str => {
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
            add_region_constraints(updated, acc_constraints, *region, &parent_regions);

            // Update the parent regions, then continue exploring
            let mut parent_regions = parent_regions.clone();
            parent_regions.insert(*region);
            compute_full_regions_constraints_for_ty(
                updated,
                constraints_map,
                acc_constraints,
                type_vars_constraints,
                parent_regions,
                ref_ty,
            );
        }
        Ty::TypeVar(var_id) => {
            // Add the parent regions in the set of parent regions for the type variable
            match type_vars_constraints {
                None => (),
                Some(type_vars_constraints) => {
                    let parents_set = type_vars_constraints.get_mut(var_id).unwrap();
                    for parent in parent_regions {
                        if !parents_set.contains(&parent) {
                            *updated = true;
                            parents_set.insert(parent);
                        }
                    }
                }
            }
        }
    }
}

/// Auxiliary function.
///
/// Compute the region constraints for a type declaration group.
///
/// Note that recursive types in rust are very general. For instance, they allow
/// non-uniform polymorphism:
/// ```
/// enum E<T1, T2> {
///   V1,
///   V2(Box<E<T2, T1>>)
/// }
/// ```
///
/// Following this, we compute the constraints by computing a fixed
/// point: for every variant of every type appearing in the type declaration
/// group, we compute a properly initialized set of constraints.
/// We then explore all those types: as long as exploring one of those types
/// leads to a new constraint, we reexplore them all.
fn compute_regions_constraints_for_type_decl_group(
    constraints_map: &mut TypesConstraintsMap,
    types: &TypeDefs,
    decl: &TypeDeclarationGroup,
) -> Vec<SCCs<Region<RegionVarId::Id>>> {
    // List the type ids in the type declaration group
    let type_ids: HashSet<TypeDefId::Id> = match decl {
        TypeDeclarationGroup::NonRec(id) => {
            let mut ids = HashSet::new();
            ids.insert(*id);
            ids
        }
        TypeDeclarationGroup::Rec(ids) => HashSet::from_iter(ids.iter().map(|id| *id)),
    };

    // Initialize the constraints map
    for id in type_ids.iter() {
        let type_def = types.get_type_def(*id).unwrap();
        let var_to_constraints = HashMap::from_iter(
            type_def
                .type_params
                .iter()
                .map(|var| (var.index, HashSet::new())),
        );
        constraints_map.insert(*id, var_to_constraints);
    }

    let mut updated = true;
    let mut acc_constraints_map: HashMap<TypeDefId::Id, LifetimeConstraints> =
        HashMap::from_iter(type_ids.iter().map(|id| (*id, LifetimeConstraints::new())));

    while updated {
        updated = false;

        // Accumulate constraints for every variant of every type
        for id in type_ids.iter() {
            let type_def = types.get_type_def(*id).unwrap();

            // Instantiate the type definition variants
            let region_params = im::Vector::from_iter(
                type_def
                    .region_params
                    .iter()
                    .map(|rvar| Region::Var(rvar.index)),
            );
            let type_params = im::Vector::from_iter(
                type_def
                    .type_params
                    .iter()
                    .map(|tvar| Ty::TypeVar(tvar.index)),
            );
            let variants_fields_tys =
                type_def.get_instantiated_variants(&region_params, &type_params);

            // Retrive the accumulated constraints for this type def
            let mut acc_constraints = acc_constraints_map.get_mut(id).unwrap();

            // Clone the type vars constraints map - we can't accumulate in the
            // original map, so we have to clone
            // TODO: this is not very efficient - though the sets should be super small
            let mut updt_type_vars_constraints = Some(constraints_map.get(id).unwrap().clone());

            // Explore the field types of all the variants
            for field_tys in variants_fields_tys.iter() {
                for ty in field_tys.iter() {
                    compute_full_regions_constraints_for_ty(
                        &mut updated,
                        constraints_map,
                        &mut acc_constraints,
                        &mut updt_type_vars_constraints,
                        im::HashSet::new(),
                        ty,
                    );
                }
            }

            // Update the type vars constraints map
            let updt_type_vars_constraints = updt_type_vars_constraints.unwrap();
            let type_vars_constraints = constraints_map.get_mut(id).unwrap();
            for (var_id, updt_set) in updt_type_vars_constraints.iter() {
                let set = type_vars_constraints.get_mut(var_id).unwrap();
                for r in updt_set.iter() {
                    set.insert(*r);
                }
            }
        }
    }

    // Compute the SCCs
    let mut sccs_vec: Vec<SCCs<Region<RegionVarId::Id>>> = Vec::new();
    for id in type_ids.iter() {
        let type_def = types.get_type_def(*id).unwrap();
        let sccs = compute_sccs_from_lifetime_constraints(
            acc_constraints_map.get(id).unwrap(),
            &type_def.region_params,
        );
        sccs_vec.push(sccs);
    }

    // Return
    sccs_vec
}

/// Compute the region hierarchy (the order between the region's lifetimes)
/// for a (group of mutually recursive) type definitions.
/// Note that [TypeDef] already contains a regions hierarchy: when translating
/// function signatures, we first translate the signature without this hierarchy,
/// then compute this hierarchy and add it to the type definition: this is
/// why this function performs in-place modifications instead of returning
/// a [RegionsGroup].
pub fn compute_regions_hierarchy_for_type_decl_group(
    constraints_map: &mut TypesConstraintsMap,
    types: &mut TypeDefs,
    decl: &TypeDeclarationGroup,
) {
    // Compute the constraints for every definition in the declaration group
    let constraints = compute_regions_constraints_for_type_decl_group(constraints_map, types, decl);

    // Compute the regions hierarchies from every set of constraints, and
    // update the type definitions
    let type_ids: Vec<TypeDefId::Id> = match decl {
        TypeDeclarationGroup::NonRec(id) => vec![*id],
        TypeDeclarationGroup::Rec(ids) => ids.clone(),
    };
    for (id, sccs) in type_ids.into_iter().zip(constraints.into_iter()) {
        let regions_group = compute_regions_hierarchy_from_constraints(sccs);

        let type_def = types.types.get_mut(id).unwrap();
        type_def.regions_hierarchy = regions_group;
    }
}

/// Compute the constraints between the different regions of a type (which
/// region lasts longer than which other region, etc.).
/// Note that the region hierarchies should already have been computed for all
/// the types: this function should be used when computing constraints for
/// **function signatures** only.
fn compute_regions_constraints_for_ty(
    constraints_map: &TypesConstraintsMap,
    acc_constraints: &mut LifetimeConstraints,
    ty: &RTy,
) {
    // We need to provide some values to [compute_full_regions_constraints_for_ty],
    // but we don't use them in the present case (they are use by this function
    // to communicate us information).
    let mut updated = false;
    let type_vars_constraints = &mut None;
    compute_full_regions_constraints_for_ty(
        &mut updated,
        constraints_map,
        acc_constraints,
        type_vars_constraints,
        im::HashSet::new(),
        ty,
    )
}

/// Compute the constraints between the different regions of a function
/// signature (which region lasts longer than which other region, etc.).
/// This is used to compute the order (in given by the region lifetime's)
/// between the regions.
/// TODO: rename. compute_ordered_regions_constraints...?
fn compute_regions_constraints_for_sig(
    types_constraints: &TypesConstraintsMap,
    sig: &FunSig,
) -> SCCs<Region<RegionVarId::Id>> {
    let mut constraints_graph = LifetimeConstraints::new();
    constraints_graph.add_node(Region::Static);

    for input_ty in &sig.inputs {
        compute_regions_constraints_for_ty(types_constraints, &mut constraints_graph, input_ty);
    }
    compute_regions_constraints_for_ty(types_constraints, &mut constraints_graph, &sig.output);

    // Compute the SCCs from the region constraints
    compute_sccs_from_lifetime_constraints(&constraints_graph, &sig.region_params)
}

/// Compute the region hierarchy (the order between the region's lifetimes)
/// for a function signature.
/// Note that [FunSig] already contains a regions hierarchy: when translating
/// function signatures, we first translate the signature without this hierarchy,
/// then compute this hierarchy and add it to the signature information.
pub fn compute_regions_hierarchy_for_sig(
    types_constraints: &TypesConstraintsMap,
    sig: &FunSig,
) -> RegionGroups {
    // Compute the constraints between the regions and group them accordingly
    let sccs = compute_regions_constraints_for_sig(types_constraints, sig);

    // Compute the regions hierarchy
    compute_regions_hierarchy_from_constraints(sccs)
}

/// Compute the region hierarchy (the order between the region's lifetimes) for
/// a set of function definitions.
pub fn compute_regions_hierarchies_for_functions(
    types_constraints: &TypesConstraintsMap,
    defs: &FunDefs,
) -> FunDefId::Vector<RegionGroups> {
    FunDefId::Vector::from_iter(
        defs.iter()
            .map(|def| compute_regions_hierarchy_for_sig(types_constraints, &def.signature)),
    )
}

impl RegionGroup {
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        T: Formatter<RegionVarId::Id>,
    {
        // The parent region groups
        let parents: Vec<String> = self.parents.iter().map(|gid| gid.to_string()).collect();
        let parents = format!("{{{}}}", parents.join(",")).to_string();

        // The regions included in the group
        let regions: Vec<String> = self
            .regions
            .iter()
            .map(|rid| ctx.format_object(*rid))
            .collect();
        let regions = format!("{{{}}}", regions.join(",")).to_string();

        // Put everything together
        format!(
            "{}{{parents={}}}={}",
            region_group_id_to_pretty_string(self.id),
            parents,
            regions
        )
        .to_string()
    }
}

fn types_vars_constraints_map_fmt_with_ctx<'a, 'b, 'c, T>(
    cs: &'a TypeVarsConstraintsMap,
    ctx: &'b T,
    indent: &'c str,
) -> String
where
    T: Formatter<&'a Region<RegionVarId::Id>>,
{
    let var_constraints: Vec<String> = cs
        .iter()
        .map(|(vid, regions)| {
            format!(
                "{}{} -> {{{}}}",
                indent,
                type_var_id_to_pretty_string(*vid),
                regions
                    .iter()
                    .map(|r| ctx.format_object(r))
                    .collect::<Vec<String>>()
                    .join(",")
            )
            .to_string()
        })
        .collect();
    var_constraints.join("\n")
}

/*fn types_constraints_map_fmt_with_ctx(cs: &TypesConstraintsMap, types: &ty::TypesDefs) -> String {
    let types_constraints: Vec<String> = cs
        .iter()
        .map(|(tid, cmap)| {
            let type_def = types.get(*tid).unwrap();
            format!(
                "{} -> {}",
                types.format_object(*tid),
                types_vars_constraints_map_fmt_with_ctx(cmap, ctx, "  ")
            )
            .to_string()
        })
        .collect();
    types_constraints.join("\n")
}*/
