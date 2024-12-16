open OfJsonBasic
open Types
open LlbcAst
open GAstOfJson

let rec ___ = ()

and raw_statement_of_json (ctx : of_json_ctx) (js : json) :
    (raw_statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Assign", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json ctx x_0 in
        let* x_1 = rvalue_of_json ctx x_1 in
        Ok (Assign (x_0, x_1))
    | `Assoc [ ("FakeRead", fake_read) ] ->
        let* fake_read = place_of_json ctx fake_read in
        Ok (FakeRead fake_read)
    | `Assoc [ ("SetDiscriminant", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json ctx x_0 in
        let* x_1 = variant_id_of_json ctx x_1 in
        Ok (SetDiscriminant (x_0, x_1))
    | `Assoc [ ("Drop", drop) ] ->
        let* drop = place_of_json ctx drop in
        Ok (Drop drop)
    | `Assoc [ ("Assert", assert_) ] ->
        let* assert_ = assertion_of_json ctx assert_ in
        Ok (Assert assert_)
    | `Assoc [ ("Call", call) ] ->
        let* call = call_of_json ctx call in
        Ok (Call call)
    | `Assoc [ ("Abort", abort) ] ->
        let* abort = abort_kind_of_json ctx abort in
        Ok (Abort abort)
    | `String "Return" -> Ok Return
    | `Assoc [ ("Break", break) ] ->
        let* break = int_of_json ctx break in
        Ok (Break break)
    | `Assoc [ ("Continue", continue) ] ->
        let* continue = int_of_json ctx continue in
        Ok (Continue continue)
    | `String "Nop" -> Ok Nop
    | `Assoc [ ("Switch", switch) ] ->
        let* switch = switch_of_json ctx switch in
        Ok (Switch switch)
    | `Assoc [ ("Loop", loop) ] ->
        let* loop = block_of_json ctx loop in
        Ok (Loop loop)
    | `Assoc [ ("Error", error) ] ->
        let* error = string_of_json ctx error in
        Ok (Error error)
    | _ -> Error "")

and statement_of_json (ctx : of_json_ctx) (js : json) :
    (statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("span", span);
          ("content", content);
          ("comments_before", comments_before);
        ] ->
        let* span = span_of_json ctx span in
        let* content = raw_statement_of_json ctx content in
        let* comments_before =
          list_of_json string_of_json ctx comments_before
        in
        Ok ({ span; content; comments_before } : statement)
    | _ -> Error "")

and block_of_json (ctx : of_json_ctx) (js : json) : (block, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("statements", statements) ] -> begin
        let* span = span_of_json ctx span in
        let* statements = list_of_json statement_of_json ctx statements in
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

and switch_of_json (ctx : of_json_ctx) (js : json) : (switch, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = operand_of_json ctx x_0 in
        let* x_1 = block_of_json ctx x_1 in
        let* x_2 = block_of_json ctx x_2 in
        Ok (If (x_0, x_1, x_2))
    | `Assoc [ ("SwitchInt", `List [ x_0; x_1; x_2; x_3 ]) ] ->
        let* x_0 = operand_of_json ctx x_0 in
        let* x_1 = integer_type_of_json ctx x_1 in
        let* x_2 =
          list_of_json
            (pair_of_json (list_of_json scalar_value_of_json) block_of_json)
            ctx x_2
        in
        let* x_3 = block_of_json ctx x_3 in
        Ok (SwitchInt (x_0, x_1, x_2, x_3))
    | `Assoc [ ("Match", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = place_of_json ctx x_0 in
        let* x_1 =
          list_of_json
            (pair_of_json (list_of_json variant_id_of_json) block_of_json)
            ctx x_1
        in
        let* x_2 = option_of_json block_of_json ctx x_2 in
        Ok (Match (x_0, x_1, x_2))
    | _ -> Error "")