(** Functions to load ULLBC ASTs from json.

    See the comments for {!GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
open Types
open Expressions
open UllbcAst

let rec ___ = ()

and block_id_of_json (ctx : of_json_ctx) (js : json) : (block_id, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with x -> BlockId.id_of_json ctx x | _ -> Error "")

and blocks_of_json (ctx : of_json_ctx) (js : json) : (blocks, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> vector_of_json (block_id_of_json ctx) (block_of_json ctx) ctx x
    | _ -> Error "")

and raw_statement_of_json (ctx : of_json_ctx) (js : json) :
    (raw_statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Assign", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json ctx x_0 in
        let* x_1 = rvalue_of_json ctx x_1 in
        Ok (Assign (x_0, x_1))
    | `Assoc [ ("Call", call) ] ->
        let* call = call_of_json ctx call in
        Ok (Call call)
    | `Assoc [ ("FakeRead", fake_read) ] ->
        let* fake_read = place_of_json ctx fake_read in
        Ok (FakeRead fake_read)
    | `Assoc [ ("SetDiscriminant", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json ctx x_0 in
        let* x_1 = variant_id_of_json ctx x_1 in
        Ok (SetDiscriminant (x_0, x_1))
    | `Assoc [ ("StorageDead", storage_dead) ] ->
        let* storage_dead = var_id_of_json ctx storage_dead in
        Ok (StorageDead storage_dead)
    | `Assoc [ ("Deinit", deinit) ] ->
        let* deinit = place_of_json ctx deinit in
        Ok (Deinit deinit)
    | `Assoc [ ("Drop", drop) ] ->
        let* drop = place_of_json ctx drop in
        Ok (Drop drop)
    | `Assoc [ ("Assert", assert_) ] ->
        let* assert_ = assertion_of_json ctx assert_ in
        Ok (Assert assert_)
    | `String "Nop" -> Ok Nop
    | _ -> Error "")

and statement_of_json (ctx : of_json_ctx) (js : json) :
    (statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("content", content) ] ->
        let* span = span_of_json ctx span in
        let* content = raw_statement_of_json ctx content in
        Ok ({ span; content } : statement)
    | _ -> Error "")

and switch_of_json (ctx : of_json_ctx) (js : json) : (switch, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ x_0; x_1 ]) ] ->
        let* x_0 = block_id_of_json ctx x_0 in
        let* x_1 = block_id_of_json ctx x_1 in
        Ok (If (x_0, x_1))
    | `Assoc [ ("SwitchInt", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = integer_type_of_json ctx x_0 in
        let* x_1 =
          list_of_json
            (pair_of_json (scalar_value_of_json ctx) (block_id_of_json ctx) ctx)
            ctx x_1
        in
        let* x_2 = block_id_of_json ctx x_2 in
        Ok (SwitchInt (x_0, x_1, x_2))
    | _ -> Error "")

and raw_terminator_of_json (ctx : of_json_ctx) (js : json) :
    (raw_terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Goto", `Assoc [ ("target", target) ]) ] ->
        let* target = block_id_of_json ctx target in
        Ok (Goto target)
    | `Assoc [ ("Switch", `Assoc [ ("discr", discr); ("targets", targets) ]) ]
      ->
        let* discr = operand_of_json ctx discr in
        let* targets = switch_of_json ctx targets in
        Ok (Switch (discr, targets))
    | `Assoc [ ("Abort", abort) ] ->
        let* abort = abort_kind_of_json ctx abort in
        Ok (Abort abort)
    | `String "Return" -> Ok Return
    | _ -> Error "")

and terminator_of_json (ctx : of_json_ctx) (js : json) :
    (terminator, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("content", content) ] ->
        let* span = span_of_json ctx span in
        let* content = raw_terminator_of_json ctx content in
        Ok ({ span; content } : terminator)
    | _ -> Error "")

and block_of_json (ctx : of_json_ctx) (js : json) : (block, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("statements", statements); ("terminator", terminator) ] ->
        let* statements = list_of_json (statement_of_json ctx) ctx statements in
        let* terminator = terminator_of_json ctx terminator in
        Ok ({ statements; terminator } : block)
    | _ -> Error "")

let expr_body_of_json (ctx : of_json_ctx) (js : json) :
    (expr_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Unstructured", body) ] ->
        let* body = gexpr_body_of_json (blocks_of_json ctx) ctx body in
        Ok body
    | _ -> Error "")

let crate_of_json (js : json) : (crate, string) result =
  gcrate_of_json expr_body_of_json js
