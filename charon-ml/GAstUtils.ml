open LlbcAst
module T = Types

(** Small utility: list the transitive parents of a region var group.
    We don't do that in an efficient manner, but it doesn't matter.

    This list *doesn't* include the current region.
 *)
let rec list_ancestor_region_groups (sg : fun_sig) (gid : T.RegionGroupId.id) :
    T.RegionGroupId.Set.t =
  let rg = T.RegionGroupId.nth sg.regions_hierarchy gid in
  let parents =
    List.fold_left
      (fun s gid ->
        (* Compute the parents *)
        let parents = list_ancestor_region_groups sg gid in
        (* Parents U current region *)
        let parents = T.RegionGroupId.Set.add gid parents in
        (* Make the union with the accumulator *)
        T.RegionGroupId.Set.union s parents)
      T.RegionGroupId.Set.empty rg.parents
  in
  parents

(** Small utility: same as {!list_ancestors_region_groups}, but returns an ordered list.  *)
let list_ordered_ancestor_region_groups (sg : fun_sig)
    (gid : T.RegionGroupId.id) : T.RegionGroupId.id list =
  let pset = list_ancestor_region_groups sg gid in
  let parents =
    List.filter
      (fun (rg : T.region_var_group) -> T.RegionGroupId.Set.mem rg.id pset)
      sg.regions_hierarchy
  in
  let parents = List.map (fun (rg : T.region_var_group) -> rg.id) parents in
  parents

let gexpr_body_get_input_vars (fbody : 'body gexpr_body) : var list =
  let locals = List.tl fbody.locals in
  Collections.List.prefix fbody.arg_count locals

let fun_body_get_input_vars (fbody : 'body gexpr_body) : var list =
  gexpr_body_get_input_vars fbody
