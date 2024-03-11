(** Functions to load LLBC ASTs from json.

    See the comments for {!Charon.GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
open Types
open LlbcAst

let assertion_of_json (js : json) : (assertion, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("cond", cond); ("expected", expected) ] ->
        let* cond = operand_of_json cond in
        let* expected = bool_of_json expected in
        Ok { cond; expected }
    | _ -> Error "")

let rec statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("content", content) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* content = raw_statement_of_json id_to_file content in
        Ok { meta; content }
    | _ -> Error "")

and raw_statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (raw_statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Assign", `List [ place; rvalue ]) ] ->
        let* place = place_of_json place in
        let* rvalue = rvalue_of_json rvalue in
        Ok (Assign (place, rvalue))
    | `Assoc [ ("FakeRead", place) ] ->
        let* place = place_of_json place in
        Ok (FakeRead place)
    | `Assoc [ ("SetDiscriminant", `List [ place; variant_id ]) ] ->
        let* place = place_of_json place in
        let* variant_id = VariantId.id_of_json variant_id in
        Ok (SetDiscriminant (place, variant_id))
    | `Assoc [ ("Drop", place) ] ->
        let* place = place_of_json place in
        Ok (Drop place)
    | `Assoc [ ("Assert", assertion) ] ->
        let* assertion = assertion_of_json assertion in
        Ok (Assert assertion)
    | `Assoc [ ("Call", call) ] ->
        let* call = call_of_json call in
        Ok (Call call)
    | `String "Panic" -> Ok Panic
    | `String "Return" -> Ok Return
    | `Assoc [ ("Break", i) ] ->
        let* i = int_of_json i in
        Ok (Break i)
    | `Assoc [ ("Continue", i) ] ->
        let* i = int_of_json i in
        Ok (Continue i)
    | `String "Nop" -> Ok Nop
    | `Assoc [ ("Sequence", `List [ st1; st2 ]) ] ->
        let* st1 = statement_of_json id_to_file st1 in
        let* st2 = statement_of_json id_to_file st2 in
        Ok (Sequence (st1, st2))
    | `Assoc [ ("Switch", tgt) ] ->
        let* switch = switch_of_json id_to_file tgt in
        Ok (Switch switch)
    | `Assoc [ ("Loop", st) ] ->
        let* st = statement_of_json id_to_file st in
        Ok (Loop st)
    | _ -> Error "")

and switch_of_json (id_to_file : id_to_file_map) (js : json) :
    (switch, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ op; st1; st2 ]) ] ->
        let* op = operand_of_json op in
        let* st1 = statement_of_json id_to_file st1 in
        let* st2 = statement_of_json id_to_file st2 in
        Ok (If (op, st1, st2))
    | `Assoc [ ("SwitchInt", `List [ op; int_ty; tgts; otherwise ]) ] ->
        let* op = operand_of_json op in
        let* int_ty = integer_type_of_json int_ty in
        let* tgts =
          list_of_json
            (pair_of_json
               (list_of_json scalar_value_of_json)
               (statement_of_json id_to_file))
            tgts
        in
        let* otherwise = statement_of_json id_to_file otherwise in
        Ok (SwitchInt (op, int_ty, tgts, otherwise))
    | `Assoc [ ("Match", `List [ p; tgts; otherwise ]) ] ->
        let* p = place_of_json p in
        let* tgts =
          list_of_json
            (pair_of_json
               (list_of_json VariantId.id_of_json)
               (statement_of_json id_to_file))
            tgts
        in
        let* otherwise =
          option_of_json (statement_of_json id_to_file) otherwise
        in
        Ok (Match (p, tgts, otherwise))
    | _ -> Error "")

let fun_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (fun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (gfun_decl_of_json (statement_of_json id_to_file) id_to_file js)

(** Strict type for the number of function declarations (see {!global_to_fun_id} below) *)
type global_id_converter = { fun_count : int } [@@deriving show]

(** Converts a global id to its corresponding function id.
    To do so, it adds the global id to the number of function declarations :
    We have the bijection [global_fun_id <=> global_id + fun_id_count].
*)
let global_to_fun_id (conv : global_id_converter) (gid : GlobalDeclId.id) :
    FunDeclId.id =
  FunDeclId.of_int (GlobalDeclId.to_int gid + conv.fun_count)

(** Deserialize a global declaration, and decompose it into a global declaration
    and a function declaration.
 *)
let global_decl_of_json (id_to_file : id_to_file_map) (js : json)
    (gid_conv : global_id_converter) : (global_decl * fun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    ((* Deserialize the global declaration *)
     let* global =
       gglobal_decl_of_json (statement_of_json id_to_file) id_to_file js
     in
     let { def_id = global_id; meta; body; is_local; name; ty; kind } =
       global
     in
     (* Decompose into a global and a function *)
     let fun_id = global_to_fun_id gid_conv global.def_id in
     let signature : fun_sig =
       {
         (* Not sure about `is_unsafe` actually *)
         is_unsafe = false;
         is_closure = false;
         closure_info = None;
         generics = TypesUtils.empty_generic_params;
         preds = TypesUtils.empty_predicates;
         parent_params_info = None;
         inputs = [];
         output = ty;
       }
     in
     let global_decl : global_decl =
       { def_id = global_id; meta; body = fun_id; is_local; name; ty; kind }
     in
     let fun_decl : fun_decl =
       {
         def_id = fun_id;
         meta;
         is_local;
         name;
         signature;
         kind = RegularKind;
         body;
         is_global_decl_body = true;
       }
     in
     Ok (global_decl, fun_decl))

let crate_of_json (js : json) : (crate, string) result =
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
          ("trait_decls", trait_decls);
          ("trait_impls", trait_impls);
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
        let type_decls =
          TypeDeclId.Map.of_list
            (List.map (fun (d : type_decl) -> (d.def_id, d)) types)
        in
        (* Concatenate the functions and the global bodies *)
        let fun_decls =
          FunDeclId.Map.of_list
            (List.map
               (fun (d : fun_decl) -> (d.def_id, d))
               (functions @ global_bodies))
        in
        let global_decls =
          GlobalDeclId.Map.of_list
            (List.map (fun (d : global_decl) -> (d.def_id, d)) globals)
        in
        (* Traits *)
        let* trait_decls =
          list_of_json (trait_decl_of_json id_to_file) trait_decls
        in
        let* trait_impls =
          list_of_json (trait_impl_of_json id_to_file) trait_impls
        in
        let trait_decls =
          TraitDeclId.Map.of_list
            (List.map (fun (d : trait_decl) -> (d.def_id, d)) trait_decls)
        in
        let trait_impls =
          TraitImplId.Map.of_list
            (List.map (fun (d : trait_impl) -> (d.def_id, d)) trait_impls)
        in
        Ok
          {
            name;
            declarations;
            type_decls;
            fun_decls;
            global_decls;
            trait_decls;
            trait_impls;
          }
    | _ -> Error "")
