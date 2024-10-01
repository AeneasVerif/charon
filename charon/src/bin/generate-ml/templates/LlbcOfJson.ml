(** Functions to load LLBC ASTs from json.

    See the comments for {!Charon.GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
open Types
open LlbcAst

(* __REPLACE0__ *)

let expr_body_of_json (id_to_file : id_to_file_map) (js : json) :
    (expr_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Structured", body) ] ->
        let* body =
          gexpr_body_of_json (block_of_json id_to_file) id_to_file body
        in
        Ok body
    | _ -> Error "")

(** Strict type for the number of function declarations (see {!global_to_fun_id} below) *)
type global_id_converter = { max_fun_id : int } [@@deriving show]

(** Converts a global id to its corresponding function id.
    To do so, it adds the global id to the number of function declarations :
    We have the bijection [global_fun_id <=> global_id + fun_id_count].
*)
let global_to_fun_id (conv : global_id_converter) (gid : GlobalDeclId.id) :
    FunDeclId.id =
  FunDeclId.of_int (GlobalDeclId.to_int gid + conv.max_fun_id)

(** Deserialize a global declaration, and decompose it into a global declaration
    and a function declaration.
 *)
let split_global (gid_conv : global_id_converter) global :
    global_decl * fun_decl =
  (* Deserialize the global declaration *)
  let { def_id = global_id; item_meta; body; generics; ty; kind } = global in
  (* Decompose into a global and a function *)
  let fun_id = global_to_fun_id gid_conv global.def_id in
  let signature : fun_sig =
    {
      (* Not sure about `is_unsafe` actually *)
      is_unsafe = false;
      is_closure = false;
      closure_info = None;
      generics;
      parent_params_info = None;
      inputs = [];
      output = ty;
    }
  in
  let global_decl : global_decl =
    { def_id = global_id; item_meta; body = fun_id; generics; ty; kind }
  in
  let fun_decl : fun_decl =
    {
      def_id = fun_id;
      item_meta;
      signature;
      kind = RegularItem;
      body;
      is_global_decl_body = true;
    }
  in
  (global_decl, fun_decl)

let crate_of_json (js : json) : (crate, string) result =
  begin
    let* crate = gcrate_of_json expr_body_of_json js in
    (* When deserializing the globals, we split the global declarations
     * between the globals themselves and their bodies, which are simply
     * functions with no arguments. We add the global bodies to the list
     * of function declarations; we give fresh ids to these new bodies
     * by incrementing from the last function id recorded *)
    let gid_conv =
      {
        max_fun_id =
          List.fold_left
            (fun acc (id, _) -> max acc (1 + FunDeclId.to_int id))
            0
            (FunDeclId.Map.bindings crate.fun_decls);
      }
    in
    let globals, global_bodies =
      List.split
        (List.map
           (fun (_, g) -> split_global gid_conv g)
           (GlobalDeclId.Map.bindings crate.global_decls))
    in

    (* Add the global bodies to the list of functions *)
    let fun_decls =
      List.fold_left
        (fun m (d : fun_decl) -> FunDeclId.Map.add d.def_id d m)
        crate.fun_decls global_bodies
    in
    let global_decls =
      GlobalDeclId.Map.of_list
        (List.map (fun (d : global_decl) -> (d.def_id, d)) globals)
    in

    Ok
      {
        name = crate.name;
        declarations = crate.declarations;
        type_decls = crate.type_decls;
        fun_decls;
        global_decls;
        trait_decls = crate.trait_decls;
        trait_impls = crate.trait_impls;
        source_files = crate.source_files;
      }
  end
