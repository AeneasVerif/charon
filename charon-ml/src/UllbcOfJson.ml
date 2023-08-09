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
    | _ -> Error "")

let switch_of_json (js : json) : (A.switch, string) result =
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

let call_of_json (js : json) : (A.raw_terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("call", call); ("target", target) ] ->
        let* call = call_of_json call in
        let* target = A.BlockId.id_of_json target in

        Ok (A.Call (call, target))
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
    | `Assoc [ ("Goto", `Assoc [ ("target", target) ]) ] ->
        let* target = A.BlockId.id_of_json target in
        Ok (A.Goto target)
    | `Assoc [ ("Switch", `Assoc [ ("discr", discr); ("targets", targets) ]) ]
      ->
        let* discr = operand_of_json discr in
        let* targets = switch_of_json targets in
        Ok (A.Switch (discr, targets))
    | `String "Panic" -> Ok A.Panic
    | `String "Return" -> Ok A.Return
    | `String "Unreachable" -> Ok A.Unreachable
    | `Assoc [ ("Drop", `Assoc [ ("place", place); ("target", target) ]) ] ->
        let* place = place_of_json place in
        let* target = A.BlockId.id_of_json target in
        Ok (A.Drop (place, target))
    | `Assoc [ ("Call", call) ] -> call_of_json call
    | `Assoc
        [
          ( "Assert",
            `Assoc
              [ ("cond", cond); ("expected", expected); ("target", target) ] );
        ] ->
        let* cond = operand_of_json cond in
        let* expected = bool_of_json expected in
        let* target = A.BlockId.id_of_json target in
        Ok (A.Assert ({ cond; expected }, target))
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
        let types =
          T.TypeDeclId.Map.of_list
            (List.map (fun (d : T.type_decl) -> (d.def_id, d)) types)
        in
        let functions =
          A.FunDeclId.Map.of_list
            (List.map (fun (d : A.fun_decl) -> (d.def_id, d)) functions)
        in
        let globals =
          A.GlobalDeclId.Map.of_list
            (List.map (fun (d : A.global_decl) -> (d.def_id, d)) globals)
        in
        Ok { A.name; declarations; types; functions; globals }
    | _ -> Error "")
