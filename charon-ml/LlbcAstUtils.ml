include GAstUtils
open Types
open LlbcAst
open Utils

(** Check if a {!type:LlbcAst.statement} contains loops *)
let statement_has_loops (st : statement) : bool =
  let obj =
    object
      inherit [_] iter_statement
      method! visit_Loop _ _ = raise Found
    end
  in
  try
    obj#visit_statement () st;
    false
  with Found -> true

(** Check if a {!type:LlbcAst.fun_decl} contains loops *)
let fun_decl_has_loops (fd : fun_decl) : bool =
  match fd.body with
  | Some body -> statement_has_loops body.body
  | None -> false

let compute_defs_maps (c : crate) :
    type_decl TypeDeclId.Map.t
    * fun_decl FunDeclId.Map.t
    * global_decl GlobalDeclId.Map.t =
  let types_map =
    List.fold_left
      (fun m (def : type_decl) -> TypeDeclId.Map.add def.def_id def m)
      TypeDeclId.Map.empty c.types
  in
  let funs_map =
    List.fold_left
      (fun m (def : fun_decl) -> FunDeclId.Map.add def.def_id def m)
      FunDeclId.Map.empty c.functions
  in
  let globals_map =
    List.fold_left
      (fun m (def : global_decl) -> GlobalDeclId.Map.add def.def_id def m)
      GlobalDeclId.Map.empty c.globals
  in
  (types_map, funs_map, globals_map)

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

(** Split a module's declarations into three maps from type/fun/global ids to
    declaration groups.
 *)
let split_declarations_to_group_maps (decls : declaration_group list) :
    type_declaration_group TypeDeclId.Map.t
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
  let module TG = G (TypeDeclId.Map) in
  let types = TG.create_map types in
  let module FG = G (FunDeclId.Map) in
  let funs = FG.create_map funs in
  let globals = GlobalDeclId.Set.of_list globals in
  (types, funs, globals)
