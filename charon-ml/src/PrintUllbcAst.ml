open PrintUtils
module T = Types
module TU = TypesUtils
module E = Expressions
module A = UllbcAst
module PT = PrintTypes
module PPV = PrintPrimitiveValues
module PE = PrintExpressions

(** Pretty-printing for ULLBC AST (generic functions) *)
module Ast = struct
  include PrintGAst

  let decls_and_fun_decl_to_ast_formatter
      (type_decls : T.type_decl T.TypeDeclId.Map.t)
      (fun_decls : A.fun_decl A.FunDeclId.Map.t)
      (global_decls : A.global_decl A.GlobalDeclId.Map.t) (fdef : A.fun_decl) :
      ast_formatter =
    gdecls_and_gfun_decl_to_ast_formatter type_decls fun_decls global_decls
      (fun decl -> global_name_to_string decl.name)
      fdef

  let rec statement_to_string (fmt : ast_formatter) (indent : string)
      (st : A.statement) : string =
    raw_statement_to_string fmt indent st.content

  and raw_statement_to_string (fmt : ast_formatter) (indent : string)
      (st : A.raw_statement) : string =
    match st with
    | A.Assign (p, rv) ->
        indent ^ PE.place_to_string fmt p ^ " := " ^ PE.rvalue_to_string fmt rv
    | A.FakeRead p -> indent ^ "fake_read " ^ PE.place_to_string fmt p
    | A.SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id *)
        indent ^ "set_discriminant(" ^ PE.place_to_string fmt p ^ ", "
        ^ T.VariantId.to_string variant_id
        ^ ")"
    | A.StorageDead var_id ->
        indent ^ "storage_dead " ^ fmt.var_id_to_string var_id
    | A.Deinit p -> indent ^ "deinit " ^ PE.place_to_string fmt p

  let switch_to_string (indent : string) (tgt : A.switch) : string =
    match tgt with
    | A.If (b0, b1) ->
        let b0 = block_id_to_string b0 in
        let b1 = block_id_to_string b1 in
        indent ^ "[true -> " ^ b0 ^ "; false -> " ^ b1 ^ "]"
    | A.SwitchInt (_int_ty, branches, otherwise) ->
        let branches =
          List.map
            (fun (sv, bid) ->
              PPV.scalar_value_to_string sv
              ^ " -> " ^ block_id_to_string bid ^ "; ")
            branches
        in
        let branches = String.concat "" branches in
        let otherwise = "_ -> " ^ block_id_to_string otherwise in
        indent ^ "[" ^ branches ^ otherwise ^ "]"

  let rec terminator_to_string (fmt : ast_formatter) (indent : string)
      (st : A.terminator) : string =
    raw_terminator_to_string fmt indent st.content

  and raw_terminator_to_string (fmt : ast_formatter) (indent : string)
      (st : A.raw_terminator) : string =
    match st with
    | A.Goto bid -> indent ^ "goto " ^ block_id_to_string bid
    | Switch (op, tgts) ->
        indent ^ "switch "
        ^ PE.operand_to_string fmt op
        ^ switch_to_string indent tgts
    | A.Panic -> indent ^ "panic"
    | A.Return -> indent ^ "return"
    | A.Unreachable -> indent ^ "unreachable"
    | A.Drop (p, bid) ->
        indent ^ "drop " ^ PE.place_to_string fmt p ^ ";\n" ^ indent ^ "goto "
        ^ block_id_to_string bid
    | A.Call (call, bid) ->
        call_to_string fmt indent call
        ^ ";\n" ^ indent ^ "goto " ^ block_id_to_string bid
    | A.Assert (a, bid) ->
        assertion_to_string fmt indent a
        ^ ";\n" ^ indent ^ "goto " ^ block_id_to_string bid

  let block_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (id : A.BlockId.id) (block : A.block) : string =
    let indent1 = indent ^ indent_incr in
    let statements =
      List.map
        (fun st -> statement_to_string fmt indent1 st ^ ";\n")
        block.A.statements
    in
    let terminator = terminator_to_string fmt indent1 block.A.terminator in
    indent ^ block_id_to_string id ^ " {\n"
    ^ String.concat "" statements
    ^ terminator ^ ";\n" ^ indent ^ "}"

  let blocks_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (blocks : A.block list) : string =
    let blocks =
      A.BlockId.mapi (block_to_string fmt indent indent_incr) blocks
    in
    String.concat "\n\n" blocks

  let fun_decl_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (def : A.fun_decl) : string =
    gfun_decl_to_string fmt indent indent_incr blocks_to_string def

  let global_decl_to_string (fmt : ast_formatter) (indent : string)
      (indent_incr : string) (def : A.global_decl) : string =
    let ety_fmt = ast_to_etype_formatter fmt in
    let ety_to_string = PT.ety_to_string ety_fmt in

    let name = fun_name_to_string def.A.name in
    let ty = ety_to_string def.A.ty in

    (* We print the declaration differently if it is opaque (no body) or transparent
     * (we have access to a body) *)
    match def.A.body with
    | None ->
        (* Put everything together *)
        indent ^ "opaque global " ^ name ^ " : " ^ ty
    | Some body ->
        let body = blocks_to_string fmt indent indent_incr body.GA.body in
        indent ^ "global " ^ name ^ " : " ^ ty ^ " =\n" ^ body
end

module PA = Ast (* local module *)

(** Pretty-printing for ASTs (functions based on a declaration context) *)
module Crate = struct
  (** Generate an [ast_formatter] by using a declaration context in combination
      with the variables local to a function's declaration *)
  let decl_ctx_and_fun_decl_to_ast_formatter
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t) (def : A.fun_decl) :
      PA.ast_formatter =
    PrintGAst.decl_ctx_and_fun_decl_to_ast_formatter type_context fun_context
      global_context
      (fun decl -> global_name_to_string decl.name)
      def

  (** Generate an [ast_formatter] by using a declaration context and a global definition *)
  let decl_ctx_and_global_decl_to_ast_formatter
      (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : 'body A.gfun_decl A.FunDeclId.Map.t)
      (global_context : 'global_decl A.GlobalDeclId.Map.t)
      (decl : A.global_decl) : PA.ast_formatter =
    let region_vars = [] in
    let type_params = [] in
    let cg_params = [] in
    let locals = match decl.body with None -> [] | Some body -> body.locals in
    let get_global_decl_name_as_string decl =
      global_name_to_string decl.A.name
    in
    PrintGAst.decl_ctx_to_ast_formatter type_context fun_context global_context
      region_vars type_params cg_params locals get_global_decl_name_as_string

  (** This function pretty-prints a type declaration by using a declaration
      context *)
  let type_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t) (decl : T.type_decl)
      : string =
    let get_global_decl_name_as_string decl =
      global_name_to_string decl.A.name
    in
    PrintGAst.ctx_and_type_decl_to_string type_context global_context
      get_global_decl_name_as_string decl

  (** This function pretty-prints a global declaration by using a declaration
      context *)
  let global_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t)
      (decl : A.global_decl) : string =
    let fmt =
      decl_ctx_and_global_decl_to_ast_formatter type_context fun_context
        global_context decl
    in
    PA.global_decl_to_string fmt "" "  " decl

  (** This function pretty-prints a function declaration by using a declaration
      context *)
  let fun_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
      (fun_context : A.fun_decl A.FunDeclId.Map.t)
      (global_context : A.global_decl A.GlobalDeclId.Map.t) (def : A.fun_decl) :
      string =
    let fmt =
      decl_ctx_and_fun_decl_to_ast_formatter type_context fun_context
        global_context def
    in
    PA.fun_decl_to_string fmt "" "  " def

  let crate_to_string (m : A.crate) : string =
    let types_defs_map, funs_defs_map, globals_defs_map =
      UllbcAstUtils.compute_defs_maps m
    in

    (* The types *)
    let type_decls =
      List.map (type_decl_to_string types_defs_map globals_defs_map) m.A.types
    in

    (* The globals *)
    let global_decls =
      List.map
        (global_decl_to_string types_defs_map funs_defs_map globals_defs_map)
        m.A.globals
    in

    (* The functions *)
    let fun_decls =
      List.map
        (fun_decl_to_string types_defs_map funs_defs_map globals_defs_map)
        m.A.functions
    in

    (* Put everything together *)
    let all_defs = List.concat [ type_decls; global_decls; fun_decls ] in
    String.concat "\n\n" all_defs
end
