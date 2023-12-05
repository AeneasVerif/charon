(** Pretty-printing for generic AST (ULLBC and LLBC) *)

open Types
open TypesUtils
open GAst
open PrintUtils
open PrintTypes
open PrintExpressions

let fn_operand_to_string (env : ('a, 'b) fmt_env) (op : fn_operand) : string =
  match op with
  | FnOpRegular func -> fn_ptr_to_string env func
  | FnOpMove p -> "move " ^ place_to_string env p

let call_to_string (env : ('a, 'b) fmt_env) (indent : string) (call : call) :
    string =
  let func = fn_operand_to_string env call.func in
  let args = List.map (operand_to_string env) call.args in
  let args = "(" ^ String.concat ", " args ^ ")" in
  let dest = place_to_string env call.dest in
  indent ^ dest ^ " := move " ^ func ^ args

let assertion_to_string (env : ('a, 'b) fmt_env) (indent : string)
    (a : assertion) : string =
  let cond = operand_to_string env a.cond in
  if a.expected then indent ^ "assert(" ^ cond ^ ")"
  else indent ^ "assert(¬" ^ cond ^ ")"

(** Small helper *)
let fun_sig_with_name_to_string (env : ('a, 'b) fmt_env) (indent : string)
    (indent_incr : string) (attribute : string option) (name : string option)
    (args : var list option) (sg : fun_sig) : string =
  let ty_to_string = ty_to_string env in

  (* Unsafe keyword *)
  let unsafe = if sg.is_unsafe then "unsafe " else "" in

  (* Generics and predicates *)
  let params, trait_clauses = generic_params_to_strings env sg.generics in
  let clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr
      sg.parent_params_info trait_clauses sg.preds
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in

  (* Return type *)
  let ret_ty = sg.output in
  let ret_ty = if ty_is_unit ret_ty then "" else " -> " ^ ty_to_string ret_ty in

  (* Arguments *)
  let args =
    match args with
    | None ->
        let args = List.map ty_to_string sg.inputs in
        String.concat ", " args
    | Some args ->
        let args = List.combine args sg.inputs in
        let args =
          List.map
            (fun (var, rty) -> var_to_string var ^ " : " ^ ty_to_string rty)
            args
        in
        String.concat ", " args
  in

  (* Put everything together *)
  let attribute = match attribute with None -> "" | Some attr -> attr ^ " " in
  let name = match name with None -> "" | Some name -> " " ^ name in
  indent ^ attribute ^ unsafe ^ "fn" ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty
  ^ clauses

let fun_sig_to_string (env : ('a, 'b) fmt_env) (indent : string)
    (indent_incr : string) (sg : fun_sig) : string =
  fun_sig_with_name_to_string env indent indent_incr None None None sg

let gfun_decl_to_string (env : ('a, 'b) fmt_env) (indent : string)
    (indent_incr : string)
    (body_to_string : ('a, 'b) fmt_env -> string -> string -> 'body -> string)
    (def : 'body gfun_decl) : string =
  (* Locally update the environment *)
  let env =
    fmt_env_update_generics_and_preds env def.signature.generics
      def.signature.preds
  in

  let sg = def.signature in

  (* Function name *)
  let name = name_to_string env def.name in

  (* We print the declaration differently if it is opaque (no body) or transparent
   * (we have access to a body) *)
  match def.body with
  | None ->
      fun_sig_with_name_to_string env indent indent_incr (Some "opaque")
        (Some name) None sg
  | Some body ->
      (* Locally update the environment *)
      let locals = List.map (fun v -> (v.index, v.name)) body.locals in
      let env = { env with locals } in

      (* Arguments *)
      let inputs = List.tl body.locals in
      let inputs, _aux_locals =
        Collections.List.split_at inputs body.arg_count
      in

      (* All the locals (with erased regions) *)
      let locals =
        List.map
          (fun var ->
            indent ^ indent_incr ^ var_to_string var ^ " : "
            ^ ty_to_string env var.var_ty
            ^ ";")
          body.locals
      in
      let locals = String.concat "\n" locals in

      (* Body *)
      let body =
        body_to_string env (indent ^ indent_incr) indent_incr body.body
      in

      (* Put everything together *)
      fun_sig_with_name_to_string env indent indent_incr None (Some name)
        (Some inputs) sg
      ^ indent ^ "\n{\n" ^ locals ^ "\n\n" ^ body ^ "\n" ^ indent ^ "}"

let trait_decl_to_string (env : ('a, 'b) fmt_env) (indent : string)
    (indent_incr : string) (def : trait_decl) : string =
  (* Locally update the environment *)
  let env = fmt_env_update_generics_and_preds env def.generics def.preds in

  let ty_to_string = ty_to_string env in

  (* Name *)
  let name = name_to_string env def.name in

  (* Generics and predicates *)
  let params, trait_clauses = generic_params_to_strings env def.generics in
  let clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr None
      trait_clauses def.preds
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in

  let indent1 = indent ^ indent_incr in

  let items =
    let parent_clauses =
      List.map
        (fun clause ->
          indent1 ^ "parent_clause_"
          ^ TraitClauseId.to_string clause.clause_id
          ^ " : "
          ^ trait_clause_to_string env clause
          ^ "\n")
        def.parent_clauses
    in
    let consts =
      List.map
        (fun (name, (ty, opt_id)) ->
          let ty = ty_to_string ty in
          let lhs = indent1 ^ "const " ^ name ^ " : " ^ ty in
          match opt_id with
          | None -> lhs ^ "\n"
          | Some id -> lhs ^ " = " ^ global_decl_id_to_string env id ^ "\n")
        def.consts
    in
    let types =
      List.map
        (fun (name, (clauses, opt_ty)) ->
          let clauses = List.map (trait_clause_to_string env) clauses in
          let clauses = clauses_to_string indent1 indent_incr 0 clauses in
          match opt_ty with
          | None -> indent1 ^ "type " ^ name ^ clauses ^ "\n"
          | Some ty ->
              indent1 ^ "type " ^ name ^ " = " ^ ty_to_string ty ^ clauses
              ^ "\n")
        def.types
    in
    let required_methods =
      List.map
        (fun (name, f) ->
          indent1 ^ "fn " ^ name ^ " : " ^ fun_decl_id_to_string env f ^ "\n")
        def.required_methods
    in
    let provided_methods =
      List.map
        (fun (name, f) ->
          match f with
          | None -> indent1 ^ "fn " ^ name ^ "\n"
          | Some f ->
              indent1 ^ "fn " ^ name ^ " : "
              ^ fun_decl_id_to_string env f
              ^ "\n")
        def.provided_methods
    in
    let items =
      List.concat
        [
          parent_clauses;
          consts;
          types;
          [ indent1 ^ "// Required methods\n" ];
          required_methods;
          [ indent1 ^ "// Provided methods\n" ];
          provided_methods;
        ]
    in
    if items = [] then "" else "\n{\n" ^ String.concat "" items ^ "}"
  in

  "trait " ^ name ^ params ^ clauses ^ items

let trait_impl_to_string (env : ('a, 'b) fmt_env) (indent : string)
    (indent_incr : string) (def : trait_impl) : string =
  (* Locally update the environment *)
  let env = fmt_env_update_generics_and_preds env def.generics def.preds in

  let ty_to_string = ty_to_string env in

  (* Name *)
  let name = name_to_string env def.name in

  (* Generics and predicates *)
  let params, trait_clauses = generic_params_to_strings env def.generics in
  let clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr None
      trait_clauses def.preds
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in

  let indent1 = indent ^ indent_incr in

  let items =
    (* The parent clauses are given by the trait refs of the implemented trait *)
    let parent_clauses =
      Collections.List.mapi
        (fun i trait_ref ->
          indent1 ^ "parent_clause" ^ string_of_int i ^ " = "
          ^ trait_ref_to_string env trait_ref
          ^ "\n")
        def.parent_trait_refs
    in
    let consts =
      List.map
        (fun (name, (ty, id)) ->
          let ty = ty_to_string ty in
          let id = global_decl_id_to_string env id in
          indent1 ^ "const " ^ name ^ " : " ^ ty ^ " = " ^ id ^ "\n")
        def.consts
    in
    let types =
      List.map
        (fun (name, (trait_refs, ty)) ->
          let trait_refs =
            if trait_refs <> [] then
              " where ["
              ^ String.concat ", "
                  (List.map (trait_ref_to_string env) trait_refs)
              ^ "]"
            else ""
          in
          indent1 ^ "type " ^ name ^ " = " ^ ty_to_string ty ^ trait_refs ^ "\n")
        def.types
    in
    let env_method (name, f) =
      indent1 ^ "fn " ^ name ^ " : " ^ fun_decl_id_to_string env f ^ "\n"
    in
    let required_methods = List.map env_method def.required_methods in
    let provided_methods = List.map env_method def.provided_methods in
    let methods =
      if required_methods <> [] || provided_methods <> [] then
        List.concat
          [
            [ indent1 ^ "// Required methods\n" ];
            required_methods;
            [ indent1 ^ "// Provided methods\n" ];
            provided_methods;
          ]
      else []
    in
    let items = List.concat [ parent_clauses; consts; types; methods ] in
    if items = [] then "" else "\n{\n" ^ String.concat "" items ^ "}"
  in

  let impl_trait = trait_decl_ref_to_string env def.impl_trait in
  "impl" ^ params ^ " " ^ name ^ params ^ " : " ^ impl_trait ^ clauses ^ items
