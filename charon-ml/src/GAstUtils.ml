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
    * GlobalDeclId.id list =
  let rec split decls =
    match decls with
    | [] -> ([], [], [])
    | d :: decls' -> (
        let types, funs, globals = split decls' in
        match d with
        | Type decl -> (decl :: types, funs, globals)
        | Fun decl -> (types, decl :: funs, globals)
        | Global decl -> (types, funs, decl :: globals))
  in
  split decls

(** Given a crate, compute maps from type/function/global ids to declarations *)
let compute_defs_maps (get_global_id : 'global_decl -> GlobalDeclId.id)
    (c : ('body gfun_decl, 'global_decl) gcrate) :
    T.type_decl T.TypeDeclId.Map.t
    * 'body gfun_decl FunDeclId.Map.t
    * 'global_decl GlobalDeclId.Map.t =
  let types_map =
    List.fold_left
      (fun m (def : T.type_decl) -> T.TypeDeclId.Map.add def.def_id def m)
      T.TypeDeclId.Map.empty c.types
  in
  let funs_map =
    List.fold_left
      (fun m (def : 'body gfun_decl) -> FunDeclId.Map.add def.def_id def m)
      FunDeclId.Map.empty c.functions
  in
  let globals_map =
    List.fold_left
      (fun m (def : 'global_decl) ->
        GlobalDeclId.Map.add (get_global_id def) def m)
      GlobalDeclId.Map.empty c.globals
  in
  (types_map, funs_map, globals_map)

(** Split a module's declarations into three maps from type/fun/global ids to
    declaration groups.
 *)
let split_declarations_to_group_maps (decls : declaration_group list) :
    type_declaration_group T.TypeDeclId.Map.t
    * fun_declaration_group FunDeclId.Map.t
    * GlobalDeclId.Set.t =
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
  let types, funs, globals = split_declarations decls in
  let module TG = G (T.TypeDeclId.Map) in
  let types = TG.create_map types in
  let module FG = G (FunDeclId.Map) in
  let funs = FG.create_map funs in
  let globals = GlobalDeclId.Set.of_list globals in
  (types, funs, globals)
