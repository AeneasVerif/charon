(** Functions to load ULLBC ASTs from json.

    See the comments for {!GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
module A = UllbcAst

let rec statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("content", content) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* content = raw_statement_of_json content in
        Ok ({ meta; content } : A.statement)
    | _ -> Error "")

and raw_statement_of_json (js : json) : (A.raw_statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Assign", `List [ place; rvalue ]) ] ->
        let* place = place_of_json place in
        let* rvalue = rvalue_of_json rvalue in
        Ok (A.Assign (place, rvalue))
    | `Assoc [ ("FakeRead", place) ] ->
        let* place = place_of_json place in
        Ok (A.FakeRead place)
    | `Assoc [ ("SetDiscriminant", `List [ place; variant_id ]) ] ->
        let* place = place_of_json place in
        let* variant_id = T.VariantId.id_of_json variant_id in
        Ok (A.SetDiscriminant (place, variant_id))
    | `Assoc [ ("StorageDead", var_id) ] ->
        let* var_id = E.VarId.id_of_json var_id in
        Ok (A.StorageDead var_id)
    | `Assoc [ ("Deinit", place) ] ->
        let* place = place_of_json place in
        Ok (A.Deinit place)
    | `Assoc [ ("AssignGlobal", `List [ dst; global ]) ] ->
        let* dst = E.VarId.id_of_json dst in
        let dst = { E.var_id = dst; projection = [] } in
        let* global = A.GlobalDeclId.id_of_json global in
        Ok (A.AssignGlobal { dst; global })
    | _ -> Error "")

let switch_targets_of_json (js : json) : (A.switch_targets, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ id0; id1 ]) ] ->
        let* id0 = A.BlockId.id_of_json id0 in
        let* id1 = A.BlockId.id_of_json id1 in
        Ok (A.If (id0, id1))
    | `Assoc [ ("SwitchInt", `List [ int_ty; tgts; otherwise ]) ] ->
        let* int_ty = integer_type_of_json int_ty in
        let* tgts =
          list_of_json
            (pair_of_json scalar_value_of_json A.BlockId.id_of_json)
            tgts
        in
        let* otherwise = A.BlockId.id_of_json otherwise in
        Ok (A.SwitchInt (int_ty, tgts, otherwise))
    | _ -> Error "")

let rec terminator_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("content", content) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* content = raw_terminator_of_json content in
        Ok ({ meta; content } : A.terminator)
    | _ -> Error "")

and raw_terminator_of_json (js : json) : (A.raw_terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Goto", `List [ id ]) ] ->
        let* id = A.BlockId.id_of_json id in
        Ok (A.Goto id)
    | `Assoc [ ("Switch", `List [ op; tgt ]) ] ->
        let* op = operand_of_json op in
        let* tgt = switch_targets_of_json tgt in
        Ok (A.Switch (op, tgt))
    | `String "Panic" -> Ok A.Panic
    | `String "Return" -> Ok A.Return
    | `String "Unreachable" -> Ok A.Unreachable
    | `Assoc [ ("Drop", `List [ place; block_id ]) ] ->
        let* place = place_of_json place in
        let* block_id = A.BlockId.id_of_json block_id in
        Ok (A.Drop (place, block_id))
    | `Assoc [ ("Call", `List [ call; block_id ]) ] ->
        let* call = call_of_json call in
        let* block_id = A.BlockId.id_of_json block_id in
        Ok (A.Call (call, block_id))
    | `Assoc [ ("Assert", `List [ assertion; block_id ]) ] ->
        let* assertion = assertion_of_json assertion in
        let* block_id = A.BlockId.id_of_json block_id in
        Ok (A.Assert (assertion, block_id))
    | _ -> Error "")

let block_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.block, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("statements", statements); ("terminator", terminator) ] ->
        let* statements =
          list_of_json (statement_of_json id_to_file) statements
        in
        let* terminator = terminator_of_json id_to_file terminator in
        Ok { A.statements; terminator }
    | _ -> Error "")

let blocks_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.block list, string) result =
  combine_error_msgs js __FUNCTION__
    (list_of_json (block_of_json id_to_file) js)

let fun_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.fun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (gfun_decl_of_json (blocks_of_json id_to_file) id_to_file js)

let global_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.global_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (let* global =
       gglobal_decl_of_json (blocks_of_json id_to_file) id_to_file js
     in
     let { def_id = global_id; meta; body; name; ty } = global in
     Ok { A.def_id = global_id; meta; body; name; ty })

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
        let* name = string_of_json name in
        let* id_to_file = id_to_file_of_json id_to_file in
        let* declarations =
          list_of_json declaration_group_of_json declarations
        in
        let* types = list_of_json (type_decl_of_json id_to_file) types in
        let* functions = list_of_json (fun_decl_of_json id_to_file) functions in
        let* globals = list_of_json (global_decl_of_json id_to_file) globals in
        Ok { A.name; declarations; types; functions; globals }
    | _ -> Error "")
