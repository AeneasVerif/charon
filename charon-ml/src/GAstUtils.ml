open GAst
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

(** Small utility: same as {!list_ancestor_region_groups}, but returns an ordered list.  *)
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

(** Split a module's declarations between types, functions and globals *)
let split_declarations (decls : declaration_group list) :
    type_declaration_group list
    * fun_declaration_group list
    * GlobalDeclId.id list
    * TraitDeclId.id list
    * TraitImplId.id list =
  let rec split decls =
    match decls with
    | [] -> ([], [], [], [], [])
    | d :: decls' -> (
        let types, funs, globals, trait_decls, trait_impls = split decls' in
        match d with
        | Type decl -> (decl :: types, funs, globals, trait_decls, trait_impls)
        | Fun decl -> (types, decl :: funs, globals, trait_decls, trait_impls)
        | Global decl -> (types, funs, decl :: globals, trait_decls, trait_impls)
        | TraitDecl decl ->
            (types, funs, globals, decl :: trait_decls, trait_impls)
        | TraitImpl decl ->
            (types, funs, globals, trait_decls, decl :: trait_impls))
  in
  split decls

(** Split a module's declarations into three maps from type/fun/global ids to
    declaration groups.
 *)
let split_declarations_to_group_maps (decls : declaration_group list) :
    type_declaration_group T.TypeDeclId.Map.t
    * fun_declaration_group FunDeclId.Map.t
    * GlobalDeclId.Set.t
    * TraitDeclId.Set.t
    * TraitImplId.Set.t =
  let module G (M : Map.S) = struct
    let add_group (map : M.key g_declaration_group M.t)
        (group : M.key g_declaration_group) : M.key g_declaration_group M.t =
      match group with
      | NonRec id -> M.add id group map
      | Rec ids -> List.fold_left (fun map id -> M.add id group map) map ids

    let create_map (groups : M.key g_declaration_group list) :
        M.key g_declaration_group M.t =
      List.fold_left add_group M.empty groups
  end in
  let types, funs, globals, trait_decls, trait_impls =
    split_declarations decls
  in
  let module TG = G (T.TypeDeclId.Map) in
  let types = TG.create_map types in
  let module FG = G (FunDeclId.Map) in
  let funs = FG.create_map funs in
  let globals = GlobalDeclId.Set.of_list globals in
  let trait_decls = TraitDeclId.Set.of_list trait_decls in
  let trait_impls = TraitImplId.Set.of_list trait_impls in
  (types, funs, globals, trait_decls, trait_impls)
