(** Functions to load LLBC ASTs from json.

    See the comments for {!GAstOfJson}
 *)

include GAstOfJson
open Yojson.Basic
open OfJsonBasic
module A = LlbcAst

let rec statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("content", content) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* content = raw_statement_of_json id_to_file content in
        Ok { A.meta; content }
    | _ -> Error "")

and raw_statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.raw_statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Assign", `List [ place; rvalue ]) ] ->
        let* place = place_of_json place in
        let* rvalue = rvalue_of_json rvalue in
        Ok (A.Assign (place, rvalue))
    | `Assoc [ ("AssignGlobal", `List [ dst; global ]) ] ->
        let* dst = E.VarId.id_of_json dst in
        let dst = { E.var_id = dst; projection = [] } in
        let* global = A.GlobalDeclId.id_of_json global in
        Ok (A.AssignGlobal { dst; global })
    | `Assoc [ ("FakeRead", place) ] ->
        let* place = place_of_json place in
        Ok (A.FakeRead place)
    | `Assoc [ ("SetDiscriminant", `List [ place; variant_id ]) ] ->
        let* place = place_of_json place in
        let* variant_id = T.VariantId.id_of_json variant_id in
        Ok (A.SetDiscriminant (place, variant_id))
    | `Assoc [ ("Drop", place) ] ->
        let* place = place_of_json place in
        Ok (A.Drop place)
    | `Assoc [ ("Assert", assertion) ] ->
        let* assertion = assertion_of_json assertion in
        Ok (A.Assert assertion)
    | `Assoc [ ("Call", call) ] ->
        let* call = call_of_json call in
        Ok (A.Call call)
    | `String "Panic" -> Ok A.Panic
    | `String "Return" -> Ok A.Return
    | `Assoc [ ("Break", i) ] ->
        let* i = int_of_json i in
        Ok (A.Break i)
    | `Assoc [ ("Continue", i) ] ->
        let* i = int_of_json i in
        Ok (A.Continue i)
    | `String "Nop" -> Ok A.Nop
    | `Assoc [ ("Sequence", `List [ st1; st2 ]) ] ->
        let* st1 = statement_of_json id_to_file st1 in
        let* st2 = statement_of_json id_to_file st2 in
        Ok (A.Sequence (st1, st2))
    | `Assoc [ ("Switch", `List [ op; tgt ]) ] ->
        let* op = operand_of_json op in
        let* tgt = switch_targets_of_json id_to_file tgt in
        Ok (A.Switch (op, tgt))
    | `Assoc [ ("Loop", st) ] ->
        let* st = statement_of_json id_to_file st in
        Ok (A.Loop st)
    | _ -> Error "")

and switch_targets_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.switch_targets, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ st1; st2 ]) ] ->
        let* st1 = statement_of_json id_to_file st1 in
        let* st2 = statement_of_json id_to_file st2 in
        Ok (A.If (st1, st2))
    | `Assoc [ ("SwitchInt", `List [ int_ty; tgts; otherwise ]) ] ->
        let* int_ty = integer_type_of_json int_ty in
        let* tgts =
          list_of_json
            (pair_of_json
               (list_of_json scalar_value_of_json)
               (statement_of_json id_to_file))
            tgts
        in
        let* otherwise = statement_of_json id_to_file otherwise in
        Ok (A.SwitchInt (int_ty, tgts, otherwise))
    | _ -> Error "")

let fun_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.fun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (gfun_decl_of_json (statement_of_json id_to_file) id_to_file js)

(** Strict type for the number of function declarations (see {!global_to_fun_id} below) *)
type global_id_converter = { fun_count : int } [@@deriving show]

(** Converts a global id to its corresponding function id.
    To do so, it adds the global id to the number of function declarations :
    We have the bijection [global_fun_id <=> global_id + fun_id_count].
*)
let global_to_fun_id (conv : global_id_converter) (gid : A.GlobalDeclId.id) :
    A.FunDeclId.id =
  A.FunDeclId.of_int (A.GlobalDeclId.to_int gid + conv.fun_count)

(** Deserialize a global declaration, and decompose it into a global declaration
    and a function declaration.
 *)
let global_decl_of_json (id_to_file : id_to_file_map) (js : json)
    (gid_conv : global_id_converter) :
    (A.global_decl * A.fun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    ((* Deserialize the global declaration *)
     let* global =
       gglobal_decl_of_json (statement_of_json id_to_file) id_to_file js
     in
     let { def_id = global_id; meta; body; name; ty } = global in
     (* Decompose into a global and a function *)
     let fun_id = global_to_fun_id gid_conv global.def_id in
     let signature : A.fun_sig =
       {
         region_params = [];
         num_early_bound_regions = 0;
         regions_hierarchy = [];
         type_params = [];
         inputs = [];
         output = TU.ety_no_regions_to_sty ty;
       }
     in
     Ok
       ( { A.def_id = global_id; meta; body_id = fun_id; name; ty },
         {
           A.def_id = fun_id;
           meta;
           name;
           signature;
           body;
           is_global_decl_body = true;
         } ))

let crate_of_json (js : json) : (A.crate, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("name", name);
          ("id_to_file", id_to_file);
          ("declarations", declarations);
          ("types", types);
          ("functions", functions);
          ("globals", globals);
        ] ->
        (* We first deserialize the declaration groups (which simply contain ids)
         * and all the declarations *butù* the globals *)
        let* name = string_of_json name in
        let* id_to_file = id_to_file_of_json id_to_file in
        let* declarations =
          list_of_json declaration_group_of_json declarations
        in
        let* types = list_of_json (type_decl_of_json id_to_file) types in
        let* functions = list_of_json (fun_decl_of_json id_to_file) functions in
        (* When deserializing the globals, we split the global declarations
         * between the globals themselves and their bodies, which are simply
         * functions with no arguments. We add the global bodies to the list
         * of function declarations: the (fresh) ids we use for those bodies
         * are simply given by: [num_functions + global_id] *)
        let gid_conv = { fun_count = List.length functions } in
        let* globals =
          list_of_json
            (fun js -> global_decl_of_json id_to_file js gid_conv)
            globals
        in
        let globals, global_bodies = List.split globals in
        Ok
          {
            A.name;
            declarations;
            types;
            functions = functions @ global_bodies;
            globals;
          }
    | _ -> Error "")
