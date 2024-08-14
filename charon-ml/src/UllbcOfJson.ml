(** Functions to load ULLBC ASTs from json.

    See the comments for {!GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
open Types
open Expressions
open UllbcAst

let rec statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("content", content) ] ->
        let* span = span_of_json id_to_file span in
        let* content = raw_statement_of_json content in
        Ok ({ span; content } : statement)
    | _ -> Error "")

and raw_statement_of_json (js : json) : (raw_statement, string) result =
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
    | `Assoc [ ("StorageDead", var_id) ] ->
        let* var_id = VarId.id_of_json var_id in
        Ok (StorageDead var_id)
    | `Assoc [ ("Deinit", place) ] ->
        let* place = place_of_json place in
        Ok (Deinit place)
    | _ -> Error "")

let switch_of_json (js : json) : (switch, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ id0; id1 ]) ] ->
        let* id0 = BlockId.id_of_json id0 in
        let* id1 = BlockId.id_of_json id1 in
        Ok (If (id0, id1))
    | `Assoc [ ("SwitchInt", `List [ int_ty; tgts; otherwise ]) ] ->
        let* int_ty = integer_type_of_json int_ty in
        let* tgts =
          list_of_json
            (pair_of_json scalar_value_of_json BlockId.id_of_json)
            tgts
        in
        let* otherwise = BlockId.id_of_json otherwise in
        Ok (SwitchInt (int_ty, tgts, otherwise))
    | _ -> Error "")

let call_of_json (js : json) : (raw_terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("call", call); ("target", target) ] ->
        let* call = call_of_json call in
        let* target = option_of_json BlockId.id_of_json target in

        Ok (Call (call, target))
    | _ -> Error "")

let rec terminator_of_json (id_to_file : id_to_file_map) (js : json) :
    (terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("content", content) ] ->
        let* span = span_of_json id_to_file span in
        let* content = raw_terminator_of_json content in
        Ok ({ span; content } : terminator)
    | _ -> Error "")

and raw_terminator_of_json (js : json) : (raw_terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Goto", `Assoc [ ("target", target) ]) ] ->
        let* target = BlockId.id_of_json target in
        Ok (Goto target)
    | `Assoc [ ("Switch", `Assoc [ ("discr", discr); ("targets", targets) ]) ]
      ->
        let* discr = operand_of_json discr in
        let* targets = switch_of_json targets in
        Ok (Switch (discr, targets))
    | `Assoc [ ("Abort", _) ] -> Ok Panic
    | `String "Return" -> Ok Return
    | `Assoc [ ("Drop", `Assoc [ ("place", place); ("target", target) ]) ] ->
        let* place = place_of_json place in
        let* target = BlockId.id_of_json target in
        Ok (Drop (place, target))
    | `Assoc [ ("Call", call) ] -> call_of_json call
    | `Assoc
        [
          ( "Assert",
            `Assoc
              [ ("cond", cond); ("expected", expected); ("target", target) ] );
        ] ->
        let* cond = operand_of_json cond in
        let* expected = bool_of_json expected in
        let* target = BlockId.id_of_json target in
        Ok (Assert ({ cond; expected }, target))
    | _ -> Error "")

let block_of_json (id_to_file : id_to_file_map) (js : json) :
    (block, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("statements", statements); ("terminator", terminator) ] ->
        let* statements =
          list_of_json (statement_of_json id_to_file) statements
        in
        let* terminator = terminator_of_json id_to_file terminator in
        Ok { statements; terminator }
    | _ -> Error "")

let blocks_of_json (id_to_file : id_to_file_map) (js : json) :
    (block list, string) result =
  combine_error_msgs js __FUNCTION__
    (list_of_json (block_of_json id_to_file) js)

let expr_body_of_json (id_to_file : id_to_file_map) (js : json) :
    (expr_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Unstructured", body) ] ->
        let* body =
          gexpr_body_of_json (blocks_of_json id_to_file) id_to_file body
        in
        Ok body
    | _ -> Error "")

let crate_of_json (js : json) : (crate, string) result =
  gcrate_of_json expr_body_of_json js
