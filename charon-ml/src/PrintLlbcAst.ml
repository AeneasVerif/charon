module T = Types
module TU = TypesUtils
module E = Expressions
module A = LlbcAst
open PrintUtils
module PT = PrintTypes
module PPV = PrintPrimitiveValues
module PE = PrintExpressions

(** Pretty-printing for LLBC AST (generic functions) *)
module Ast = struct
  include PrintGAst

  let decls_and_fun_decl_to_ast_formatter
      (type_decls : T.type_decl T.TypeDeclId.Map.t)
      (fun_decls : A.fun_decl A.FunDeclId.Map.t)
      (global_decls : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (fdef : A.fun_decl) :
      ast_formatter =
    gdecls_and_gfun_decl_to_ast_formatter type_decls fun_decls global_decls
      trait_decls trait_impls
      (fun decl -> global_name_to_string decl.name)
      fdef

  let rec statement_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (st : A.statement) : string =
    raw_statement_to_string fmt indent indent_incr st.content

  and raw_statement_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (st : A.raw_statement) : string =
    match st with
    | A.Assign (p, rv) ->
        indent ^ PE.place_to_string fmt p ^ " := " ^ PE.rvalue_to_string fmt rv
    | A.FakeRead p -> indent ^ "fake_read " ^ PE.place_to_string fmt p
    | A.SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id *)
        indent ^ "set_discriminant(" ^ PE.place_to_string fmt p ^ ", "
        ^ T.VariantId.to_string variant_id
        ^ ")"
    | A.Drop p -> indent ^ "drop " ^ PE.place_to_string fmt p
    | A.Assert a -> assertion_to_string fmt indent a
    | A.Call call -> call_to_string fmt indent call
    | A.Panic -> indent ^ "panic"
    | A.Return -> indent ^ "return"
    | A.Break i -> indent ^ "break " ^ string_of_int i
    | A.Continue i -> indent ^ "continue " ^ string_of_int i
    | A.Nop -> indent ^ "nop"
    | A.Sequence (st1, st2) ->
        statement_to_string fmt indent indent_incr st1
        ^ ";\n"
        ^ statement_to_string fmt indent indent_incr st2
    | A.Switch switch -> (
        match switch with
        | A.If (op, true_st, false_st) ->
            let op = PE.operand_to_string fmt op in
            let inner_indent = indent ^ indent_incr in
            let inner_to_string =
              statement_to_string fmt inner_indent indent_incr
            in
            let true_st = inner_to_string true_st in
            let false_st = inner_to_string false_st in
            indent ^ "if (" ^ op ^ ") {\n" ^ true_st ^ "\n" ^ indent ^ "}\n"
            ^ indent ^ "else {\n" ^ false_st ^ "\n" ^ indent ^ "}"
        | A.SwitchInt (op, _ty, branches, otherwise) ->
            let op = PE.operand_to_string fmt op in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 =
              statement_to_string fmt indent2 indent_incr
            in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    List.map
                      (fun sv -> "| " ^ PPV.scalar_value_to_string sv)
                      svl
                  in
                  let svl = String.concat " " svl in
                  indent ^ svl ^ " => {\n" ^ inner_to_string2 be ^ "\n"
                  ^ indent1 ^ "}")
                branches
            in
            let branches = String.concat "\n" branches in
            let branches =
              branches ^ "\n" ^ indent1 ^ "_ => {\n"
              ^ inner_to_string2 otherwise ^ "\n" ^ indent1 ^ "}"
            in
            indent ^ "switch (" ^ op ^ ") {\n" ^ branches ^ "\n" ^ indent ^ "}"
        | A.Match (p, branches, otherwise) ->
            let p = PE.place_to_string fmt p in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 =
              statement_to_string fmt indent2 indent_incr
            in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    List.map (fun sv -> "| " ^ T.VariantId.to_string sv) svl
                  in
                  let svl = String.concat " " svl in
                  indent ^ svl ^ " => {\n" ^ inner_to_string2 be ^ "\n"
                  ^ indent1 ^ "}")
                branches
            in
            let branches = String.concat "\n" branches in
            let branches =
              branches ^ "\n" ^ indent1 ^ "_ => {\n"
              ^ inner_to_string2 otherwise ^ "\n" ^ indent1 ^ "}"
            in
            indent ^ "match (" ^ p ^ ") {\n" ^ branches ^ "\n" ^ indent ^ "}")
    | A.Loop loop_st ->
        indent ^ "loop {\n"
        ^ statement_to_string fmt (indent ^ indent_incr) indent_incr loop_st
        ^ "\n" ^ indent ^ "}"

  let fun_sig_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (sg : A.fun_sig) : string =
    fun_sig_to_string fmt indent indent_incr sg

  let fun_decl_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (def : A.fun_decl) : string =
    gfun_decl_to_string fmt indent indent_incr statement_to_string def

  let global_decl_to_string (fmt : ast_formatter) (indent : string)
      (_indent_incr : string) (def : A.global_decl) : string =
    let ety_fmt = ast_to_etype_formatter fmt in
    let ety_to_string = PT.ety_to_string ety_fmt in

    (* Global name *)
    let name = global_name_to_string def.A.name in

    (* Type *)
    let ty = ety_to_string def.ty in

    let body_id = fmt.fun_decl_id_to_string def.body_id in
    indent ^ "global " ^ name ^ " : " ^ ty ^ " = " ^ body_id
end

module PA = Ast (* local module *)

(** Pretty-printing for ASTs (functions based on a declaration context) *)
module Crate = struct
  (** Generate an [ast_formatter] by using a declaration context in combination
      with the variables local to a function declaration *)
  let decl_ctx_and_fun_decl_to_ast_formatter
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (def : A.fun_decl) :
      PA.ast_formatter =
    PrintGAst.decl_ctx_and_fun_decl_to_ast_formatter type_context fun_context
      global_context trait_decls trait_impls
      (fun decl -> global_name_to_string decl.name)
      def

  (** Generate an [ast_formatter] by using a declaration context and a global definition *)
  let decl_ctx_and_global_decl_to_ast_formatter
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : 'body A.gfun_decl A.FunDeclId.Map.t)
      (global_context : 'global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (_decl : A.global_decl) :
      PA.ast_formatter =
    let generics = TypesUtils.mk_empty_generic_params in
    let locals = None in
    let get_global_decl_name_as_string decl =
      global_name_to_string decl.A.name
    in
    PrintGAst.gdecls_to_ast_formatter type_context fun_context global_context
      trait_decls trait_impls generics locals get_global_decl_name_as_string

  (** Generate an [ast_formatter] by using a declaration context in combination
      with the variables local to a trait declaration *)
  let decl_ctx_and_trait_decl_to_ast_formatter
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (def : A.trait_decl) :
      PA.ast_formatter =
    PrintGAst.decl_ctx_and_trait_decl_to_ast_formatter type_context fun_context
      global_context trait_decls trait_impls
      (fun decl -> global_name_to_string decl.name)
      def

  (** Generate an [ast_formatter] by using a declaration context in combination
      with the variables local to a trait implementation *)
  let decl_ctx_and_trait_impl_to_ast_formatter
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (def : A.trait_impl) :
      PA.ast_formatter =
    PrintGAst.decl_ctx_and_trait_impl_to_ast_formatter type_context fun_context
      global_context trait_decls trait_impls
      (fun decl -> global_name_to_string decl.name)
      def

  (** This function pretty-prints a type declaration by using a declaration
      context *)
  let type_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (global_context : A.global_decl T.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (decl : T.type_decl) :
      string =
    let get_global_decl_name_as_string decl =
      global_name_to_string decl.A.name
    in
    PrintGAst.ctx_and_type_decl_to_string type_context global_context
      trait_decls trait_impls get_global_decl_name_as_string decl

  (** This function pretty-prints a global declaration by using a declaration
      context *)
  let global_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (decl : A.global_decl) :
      string =
    let fmt =
      decl_ctx_and_global_decl_to_ast_formatter type_context fun_context
        global_context trait_decls trait_impls decl
    in
    PA.global_decl_to_string fmt "" "  " decl

  (** This function pretty-prints a function declaration by using a declaration
      context *)
  let fun_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (def : A.fun_decl) :
      string =
    let fmt =
      decl_ctx_and_fun_decl_to_ast_formatter type_context fun_context
        global_context trait_decls trait_impls def
    in
    PA.fun_decl_to_string fmt "" "  " def

  (** This function pretty-prints a trait declaration by using a declaration
      context *)
  let trait_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (def : A.trait_decl) :
      string =
    let fmt =
      decl_ctx_and_trait_decl_to_ast_formatter type_context fun_context
        global_context trait_decls trait_impls def
    in
    PA.trait_decl_to_string fmt "" "  " def

  (** This function pretty-prints a trait implementation by using a declaration
      context *)
  let trait_impl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (trait_decls : A.trait_decl A.TraitDeclId.Map.t)
      (trait_impls : A.trait_impl A.TraitImplId.Map.t) (def : A.trait_impl) :
      string =
    let fmt =
      decl_ctx_and_trait_impl_to_ast_formatter type_context fun_context
        global_context trait_decls trait_impls def
    in
    PA.trait_impl_to_string fmt "" "  " def

  let crate_type_decl_to_string (m : A.crate) (decl : T.type_decl) : string =
    type_decl_to_string m.types m.globals m.trait_decls m.trait_impls decl

  let crate_global_decl_to_string (m : A.crate) (decl : A.global_decl) : string
      =
    global_decl_to_string m.types m.functions m.globals m.trait_decls
      m.trait_impls decl

  let crate_fun_decl_to_string (m : A.crate) (decl : A.fun_decl) : string =
    fun_decl_to_string m.types m.functions m.globals m.trait_decls m.trait_impls
      decl

  let crate_to_string (m : A.crate) : string =
    (* The types *)
    let type_decls =
      List.map
        (fun (_, d) ->
          type_decl_to_string m.types m.globals m.trait_decls m.trait_impls d)
        (T.TypeDeclId.Map.bindings m.A.types)
    in

    (* The globals *)
    let global_decls =
      List.map
        (fun (_, d) ->
          global_decl_to_string m.types m.functions m.globals m.trait_decls
            m.trait_impls d)
        (A.GlobalDeclId.Map.bindings m.A.globals)
    in

    (* The functions *)
    let fun_decls =
      List.map
        (fun (_, d) ->
          fun_decl_to_string m.types m.functions m.globals m.trait_decls
            m.trait_impls d)
        (A.FunDeclId.Map.bindings m.A.functions)
    in

    (* The trait declarations *)
    let trait_decls =
      List.map
        (fun (_, d) ->
          trait_decl_to_string m.types m.functions m.globals m.trait_decls
            m.trait_impls d)
        (A.TraitDeclId.Map.bindings m.A.trait_decls)
    in

    (* The trait implementations *)
    let trait_impls =
      List.map
        (fun (_, d) ->
          trait_impl_to_string m.types m.functions m.globals m.trait_decls
            m.trait_impls d)
        (A.TraitImplId.Map.bindings m.A.trait_impls)
    in

    (* Put everything together *)
    let all_defs =
      List.concat
        [ type_decls; global_decls; trait_decls; trait_impls; fun_decls ]
    in
    String.concat "\n\n" all_defs
end
