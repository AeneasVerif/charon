(** Functions to load LLBC ASTs from json.

    See the comments for {!Charon.GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
open Types
open LlbcAst

let rec ___ = ()

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
    | `Assoc [ ("Abort", _) ] -> Ok Panic
    | `String "Return" -> Ok Return
    | `Assoc [ ("Break", i) ] ->
        let* i = int_of_json i in
        Ok (Break i)
    | `Assoc [ ("Continue", i) ] ->
        let* i = int_of_json i in
        Ok (Continue i)
    | `String "Nop" -> Ok Nop
    | `Assoc [ ("Switch", tgt) ] ->
        let* switch = switch_of_json id_to_file tgt in
        Ok (Switch switch)
    | `Assoc [ ("Loop", st) ] ->
        let* st = block_of_json id_to_file st in
        Ok (Loop st)
    | `Assoc [ ("Error", s) ] ->
        let* s = string_of_json s in
        Ok (Error s)
    | _ -> Error "")

and statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("span", span);
          ("content", content);
          ("comments_before", comments_before);
        ] ->
        let* span = span_of_json id_to_file span in
        let* content = raw_statement_of_json id_to_file content in
        let* comments_before = list_of_json string_of_json comments_before in
        Ok ({ span; content; comments_before } : statement)
    | _ -> Error "")

and block_of_json (id_to_file : id_to_file_map) (js : json) :
    (block, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("statements", statements) ] -> begin
        let* span = span_of_json id_to_file span in
        let* statements =
          list_of_json (statement_of_json id_to_file) statements
        in
        match List.rev statements with
        | [] -> Ok { span; content = Nop; comments_before = [] }
        | last :: rest ->
            let seq =
              List.fold_left
                (fun acc st ->
                  {
                    span = st.span;
                    content = Sequence (st, acc);
                    comments_before = [];
                  })
                last rest
            in
            Ok seq
      end
    | _ -> Error "")

and switch_of_json (id_to_file : id_to_file_map) (js : json) :
    (switch, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = operand_of_json x_0 in
        let* x_1 = block_of_json id_to_file x_1 in
        let* x_2 = block_of_json id_to_file x_2 in
        Ok (If (x_0, x_1, x_2))
    | `Assoc [ ("SwitchInt", `List [ x_0; x_1; x_2; x_3 ]) ] ->
        let* x_0 = operand_of_json x_0 in
        let* x_1 = integer_type_of_json x_1 in
        let* x_2 =
          list_of_json
            (pair_of_json
               (list_of_json scalar_value_of_json)
               (block_of_json id_to_file))
            x_2
        in
        let* x_3 = block_of_json id_to_file x_3 in
        Ok (SwitchInt (x_0, x_1, x_2, x_3))
    | `Assoc [ ("Match", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = place_of_json x_0 in
        let* x_1 =
          list_of_json
            (pair_of_json
               (list_of_json variant_id_of_json)
               (block_of_json id_to_file))
            x_1
        in
        let* x_2 = option_of_json (block_of_json id_to_file) x_2 in
        Ok (Match (x_0, x_1, x_2))
    | _ -> Error "")

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

let crate_of_json (js : json) : (crate, string) result =
  gcrate_of_json expr_body_of_json js
