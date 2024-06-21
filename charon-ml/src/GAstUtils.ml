open Types
open GAst

(** Small utility: list the transitive parents of a region var group.
    We don't do that in an efficient manner, but it doesn't matter.

    This list *doesn't* include the current region.
 *)
let rec list_ancestor_region_groups (regions_hierarchy : region_var_groups)
    (gid : RegionGroupId.id) : RegionGroupId.Set.t =
  let rg = RegionGroupId.nth regions_hierarchy gid in
  let parents =
    List.fold_left
      (fun s gid ->
        (* Compute the parents *)
        let parents = list_ancestor_region_groups regions_hierarchy gid in
        (* Parents U current region *)
        let parents = RegionGroupId.Set.add gid parents in
        (* Make the union with the accumulator *)
        RegionGroupId.Set.union s parents)
      RegionGroupId.Set.empty rg.parents
  in
  parents

(** Small utility: same as {!list_ancestor_region_groups}, but returns an ordered list.  *)
let list_ordered_ancestor_region_groups (regions_hierarchy : region_var_groups)
    (gid : RegionGroupId.id) : RegionGroupId.id list =
  let pset = list_ancestor_region_groups regions_hierarchy gid in
  let parents =
    List.filter
      (fun (rg : region_var_group) -> RegionGroupId.Set.mem rg.id pset)
      regions_hierarchy
  in
  let parents = List.map (fun (rg : region_var_group) -> rg.id) parents in
  parents

let gexpr_body_get_input_vars (fbody : 'body gexpr_body) : var list =
  let locals = List.tl fbody.locals in
  Collections.List.prefix fbody.arg_count locals

let fun_body_get_input_vars (fbody : 'body gexpr_body) : var list =
  gexpr_body_get_input_vars fbody

let g_declaration_group_to_list (g : 'a g_declaration_group) : 'a list =
  match g with RecGroup ids -> ids | NonRecGroup id -> [ id ]

(** Split a module's declarations between types, functions and globals *)
let split_declarations (decls : declaration_group list) :
    type_declaration_group list
    * fun_declaration_group list
    * GlobalDeclId.id list
    * trait_declaration_group list
    * TraitImplId.id list
    * mixed_declaration_group list =
  let rec split decls =
    match decls with
    | [] -> ([], [], [], [], [], [])
    | d :: decls' -> (
        let types, funs, globals, trait_decls, trait_impls, mixeds =
          split decls'
        in
        match d with
        | TypeGroup decl ->
            (decl :: types, funs, globals, trait_decls, trait_impls, mixeds)
        | FunGroup decl ->
            (types, decl :: funs, globals, trait_decls, trait_impls, mixeds)
        | GlobalGroup decl ->
            (types, funs, decl :: globals, trait_decls, trait_impls, mixeds)
        | TraitDeclGroup decl ->
            (types, funs, globals, decl :: trait_decls, trait_impls, mixeds)
        | TraitImplGroup decl ->
            (types, funs, globals, trait_decls, decl :: trait_impls, mixeds)
        | MixedGroup decls ->
            (types, funs, globals, trait_decls, trait_impls, decls :: mixeds))
  in
  split decls

(** Split a module's declarations into three maps from type/fun/global ids to
    declaration groups.
 *)
let split_declarations_to_group_maps (decls : declaration_group list) :
    type_declaration_group TypeDeclId.Map.t
    * fun_declaration_group FunDeclId.Map.t
    * GlobalDeclId.Set.t
    * trait_declaration_group TraitDeclId.Map.t
    * TraitImplId.Set.t =
  let module G (M : Map.S) = struct
    let add_group (map : M.key g_declaration_group M.t)
        (group : M.key g_declaration_group) : M.key g_declaration_group M.t =
      match group with
      | NonRecGroup id -> M.add id group map
      | RecGroup ids ->
          List.fold_left (fun map id -> M.add id group map) map ids

    let create_map (groups : M.key g_declaration_group list) :
        M.key g_declaration_group M.t =
      List.fold_left add_group M.empty groups
  end in
  let types, funs, globals, trait_decls, trait_impls, mixed_groups =
    split_declarations decls
  in
  if List.length mixed_groups <> 0 then
    raise (Failure "Mixed declaration groups cannot be indexed by declaration");
  let module TG = G (TypeDeclId.Map) in
  let types = TG.create_map types in
  let module FG = G (FunDeclId.Map) in
  let funs = FG.create_map funs in
  let globals = GlobalDeclId.Set.of_list globals in
  let module TDG = G (TraitDeclId.Map) in
  let trait_decls = TDG.create_map trait_decls in
  let trait_impls = TraitImplId.Set.of_list trait_impls in
  (types, funs, globals, trait_decls, trait_impls)
