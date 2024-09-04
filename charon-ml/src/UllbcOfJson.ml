(** Functions to load ULLBC ASTs from json.

    See the comments for {!GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
open Types
open Expressions
open UllbcAst

let block_id_of_json = BlockId.id_of_json

let rec ___ = ()

and statement_of_json (id_to_file : id_to_file_map) (js : json) :
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
    | `Assoc [ ("Assign", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json x_0 in
        let* x_1 = rvalue_of_json x_1 in
        Ok (Assign (x_0, x_1))
    | `Assoc [ ("FakeRead", fake_read) ] ->
        let* fake_read = place_of_json fake_read in
        Ok (FakeRead fake_read)
    | `Assoc [ ("SetDiscriminant", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json x_0 in
        let* x_1 = variant_id_of_json x_1 in
        Ok (SetDiscriminant (x_0, x_1))
    | `Assoc [ ("StorageDead", storage_dead) ] ->
        let* storage_dead = var_id_of_json storage_dead in
        Ok (StorageDead storage_dead)
    | `Assoc [ ("Deinit", deinit) ] ->
        let* deinit = place_of_json deinit in
        Ok (Deinit deinit)
    | `Assoc [ ("Assert", assert_) ] ->
        let* assert_ = assertion_of_json assert_ in
        Ok (StAssert assert_)
    | _ -> Error "")

and switch_of_json (js : json) : (switch, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ x_0; x_1 ]) ] ->
        let* x_0 = block_id_of_json x_0 in
        let* x_1 = block_id_of_json x_1 in
        Ok (If (x_0, x_1))
    | `Assoc [ ("SwitchInt", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = integer_type_of_json x_0 in
        let* x_1 =
          list_of_json (pair_of_json scalar_value_of_json block_id_of_json) x_1
        in
        let* x_2 = block_id_of_json x_2 in
        Ok (SwitchInt (x_0, x_1, x_2))
    | _ -> Error "")

and terminator_of_json (id_to_file : id_to_file_map) (js : json) :
    (terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("content", content) ] ->
        let* span = span_of_json id_to_file span in
        let* content = raw_terminator_of_json id_to_file content in
        Ok ({ span; content } : terminator)
    | _ -> Error "")

and raw_terminator_of_json (id_to_file : id_to_file_map) (js : json) :
    (raw_terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Goto", `Assoc [ ("target", target) ]) ] ->
        let* target = block_id_of_json target in
        Ok (Goto target)
    | `Assoc [ ("Switch", `Assoc [ ("discr", discr); ("targets", targets) ]) ]
      ->
        let* discr = operand_of_json discr in
        let* targets = switch_of_json targets in
        Ok (Switch (discr, targets))
    | `Assoc [ ("Abort", abort) ] ->
        let* abort = abort_kind_of_json id_to_file abort in
        Ok (Abort abort)
    | `String "Return" -> Ok Return
    | `Assoc [ ("Drop", `Assoc [ ("place", place); ("target", target) ]) ] ->
        let* place = place_of_json place in
        let* target = block_id_of_json target in
        Ok (Drop (place, target))
    | `Assoc [ ("Call", `Assoc [ ("call", call); ("target", target) ]) ] ->
        let* call = call_of_json call in
        let* target = option_of_json block_id_of_json target in
        Ok (Call (call, target))
    | `Assoc [ ("Assert", `Assoc [ ("assert", assert_); ("target", target) ]) ]
      ->
        let* assert_ = assertion_of_json assert_ in
        let* target = block_id_of_json target in
        Ok (Assert (assert_, target))
    | _ -> Error "")

and block_of_json (id_to_file : id_to_file_map) (js : json) :
    (block, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("statements", statements); ("terminator", terminator) ] ->
        let* statements =
          list_of_json (statement_of_json id_to_file) statements
        in
        let* terminator = terminator_of_json id_to_file terminator in
        Ok ({ statements; terminator } : block)
    | _ -> Error "")

and blocks_of_json (id_to_file : id_to_file_map) (js : json) :
    (blocks, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> vector_of_json block_id_of_json (block_of_json id_to_file) x
    | _ -> Error "")

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
