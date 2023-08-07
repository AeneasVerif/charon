(** Pretty-printing for generic AST (ULLBC and LLBC) *)

module T = Types
module TU = TypesUtils
module E = Expressions
module GA = GAst
open PrintUtils
module PT = PrintTypes
module PE = PrintExpressions

type ast_formatter = PE.expr_formatter

let ast_to_etype_formatter : ast_formatter -> PT.etype_formatter =
  PE.expr_to_etype_formatter

let ast_to_rtype_formatter : ast_formatter -> PT.rtype_formatter =
  PE.expr_to_rtype_formatter

let ast_to_stype_formatter : ast_formatter -> PT.stype_formatter =
  PE.expr_to_stype_formatter

let gdecls_and_gfun_decl_to_ast_formatter
    (type_decls : T.type_decl T.TypeDeclId.Map.t)
    (fun_decls : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_decls : 'gdecl GA.GlobalDeclId.Map.t)
    (get_global_decl_name_as_string : 'gdecl -> string)
    (fdef : 'body GA.gfun_decl) : ast_formatter =
  let rvar_to_string r =
    let rvar = T.RegionVarId.nth fdef.signature.region_params r in
    PT.region_var_to_string rvar
  in
  let r_to_string r = PT.region_id_to_string r in

  let type_var_id_to_string vid =
    let var = T.TypeVarId.nth fdef.signature.type_params vid in
    PT.type_var_to_string var
  in
  let const_generic_var_id_to_string vid =
    let var = T.ConstGenericVarId.nth fdef.signature.const_generic_params vid in
    PT.const_generic_var_to_string var
  in
  let type_decl_id_to_string def_id =
    let def = T.TypeDeclId.Map.find def_id type_decls in
    name_to_string def.name
  in
  let adt_variant_to_string =
    PT.type_ctx_to_adt_variant_to_string_fun type_decls
  in
  let var_id_to_string vid =
    let var = E.VarId.nth (Option.get fdef.body).locals vid in
    var_to_string var
  in
  let adt_field_names = PT.type_ctx_to_adt_field_names_fun type_decls in
  let adt_field_to_string = PT.type_ctx_to_adt_field_to_string_fun type_decls in
  let fun_decl_id_to_string def_id =
    let def = GA.FunDeclId.Map.find def_id fun_decls in
    fun_name_to_string def.name
  in
  let global_decl_id_to_string def_id =
    let def = GA.GlobalDeclId.Map.find def_id global_decls in
    get_global_decl_name_as_string def
  in
  {
    rvar_to_string;
    r_to_string;
    type_var_id_to_string;
    type_decl_id_to_string;
    const_generic_var_id_to_string;
    adt_variant_to_string;
    var_id_to_string;
    adt_field_names;
    adt_field_to_string;
    fun_decl_id_to_string;
    global_decl_id_to_string;
  }

let call_to_string (fmt : ast_formatter) (indent : string) (call : GA.call) :
    string =
  let ty_fmt = ast_to_etype_formatter fmt in
  let t_params =
    if List.length call.GA.type_args > 0 then
      "<"
      ^ String.concat "," (List.map (PT.ty_to_string ty_fmt) call.GA.type_args)
      ^ ">"
    else ""
  in
  let args = List.map (PE.operand_to_string fmt) call.GA.args in
  let args = "(" ^ String.concat ", " args ^ ")" in
  let name_args =
    match call.GA.func with
    | GA.Regular fid -> fmt.fun_decl_id_to_string fid ^ t_params
    | GA.Assumed fid -> (
        match fid with
        | GA.Replace -> "core::mem::replace" ^ t_params
        | GA.BoxNew -> "alloc::boxed::Box" ^ t_params ^ "::new"
        | GA.BoxDeref -> "core::ops::deref::Deref<Box" ^ t_params ^ ">::deref"
        | GA.BoxDerefMut ->
            "core::ops::deref::DerefMut" ^ t_params ^ "::deref_mut"
        | GA.BoxFree -> "alloc::alloc::box_free" ^ t_params
        | GA.VecNew -> "alloc::vec::Vec" ^ t_params ^ "::new"
        | GA.VecPush -> "alloc::vec::Vec" ^ t_params ^ "::push"
        | GA.VecInsert -> "alloc::vec::Vec" ^ t_params ^ "::insert"
        | GA.VecLen -> "alloc::vec::Vec" ^ t_params ^ "::len"
        | GA.VecIndex ->
            "core::ops::index::Index<alloc::vec::Vec" ^ t_params ^ ">::index"
        | GA.VecIndexMut ->
            "core::ops::index::IndexMut<alloc::vec::Vec" ^ t_params
            ^ ">::index_mut"
        | GA.ArrayIndexShared -> "@ArrayIndexShared" ^ t_params
        | GA.ArrayIndexMut -> "@ArrayIndexMut" ^ t_params
        | GA.ArrayToSliceShared -> "@ArrayToSliceShared" ^ t_params
        | GA.ArrayToSliceMut -> "@ArrayToSliceMut" ^ t_params
        | GA.ArraySubsliceShared -> "@ArraySubsliceShared" ^ t_params
        | GA.ArraySubsliceMut -> "@ArraySubsliceMut" ^ t_params
        | GA.SliceLen -> "@SliceLen" ^ t_params
        | GA.SliceIndexShared -> "@SliceIndexShared" ^ t_params
        | GA.SliceIndexMut -> "@SliceIndexMut" ^ t_params
        | GA.SliceSubsliceShared -> "@SliceSubsliceShared" ^ t_params
        | GA.SliceSubsliceMut -> "@SliceSubsliceMut" ^ t_params)
  in
  let dest = PE.place_to_string fmt call.GA.dest in
  indent ^ dest ^ " := move " ^ name_args ^ args

let assertion_to_string (fmt : ast_formatter) (indent : string)
    (a : GA.assertion) : string =
  let cond = PE.operand_to_string fmt a.GA.cond in
  if a.GA.expected then indent ^ "assert(" ^ cond ^ ")"
  else indent ^ "assert(¬" ^ cond ^ ")"

let gfun_decl_to_string (fmt : ast_formatter) (indent : string)
    (indent_incr : string)
    (body_to_string : ast_formatter -> string -> string -> 'body -> string)
    (def : 'body GA.gfun_decl) : string =
  let sty_fmt = ast_to_stype_formatter fmt in
  let sty_to_string = PT.sty_to_string sty_fmt in
  let ety_fmt = ast_to_etype_formatter fmt in
  let ety_to_string = PT.ety_to_string ety_fmt in
  let sg = def.signature in

  (* Function name *)
  let name = fun_name_to_string def.GA.name in

  (* Region/type parameters *)
  let regions = sg.region_params in
  let types = sg.type_params in
  let params =
    if List.length regions + List.length types = 0 then ""
    else
      let regions = List.map PT.region_var_to_string regions in
      let types = List.map PT.type_var_to_string types in
      "<" ^ String.concat "," (List.append regions types) ^ ">"
  in

  (* Return type *)
  let ret_ty = sg.output in
  let ret_ty =
    if TU.ty_is_unit ret_ty then "" else " -> " ^ sty_to_string ret_ty
  in

  (* We print the declaration differently if it is opaque (no body) or transparent
   * (we have access to a body) *)
  match def.body with
  | None ->
      (* Arguments *)
      let input_tys = sg.inputs in
      let args = List.map sty_to_string input_tys in
      let args = String.concat ", " args in

      (* Put everything together *)
      indent ^ "opaque fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty
  | Some body ->
      (* Arguments *)
      let inputs = List.tl body.locals in
      let inputs, _aux_locals =
        Collections.List.split_at inputs body.arg_count
      in
      let args = List.combine inputs sg.inputs in
      let args =
        List.map
          (fun (var, rty) -> var_to_string var ^ " : " ^ sty_to_string rty)
          args
      in
      let args = String.concat ", " args in

      (* All the locals (with erased regions) *)
      let locals =
        List.map
          (fun var ->
            indent ^ indent_incr ^ var_to_string var ^ " : "
            ^ ety_to_string var.var_ty ^ ";")
          body.locals
      in
      let locals = String.concat "\n" locals in

      (* Body *)
      let body =
        body_to_string fmt (indent ^ indent_incr) indent_incr body.body
      in

      (* Put everything together *)
      indent ^ "fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty ^ " {\n"
      ^ locals ^ "\n\n" ^ body ^ "\n" ^ indent ^ "}"

(** This function pretty-prints a type definition by using a definition context *)
let ctx_and_type_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
    (global_context : 'global_decl GA.GlobalDeclId.Map.t)
    (get_global_decl_name_as_string : 'gdecl -> string) (decl : T.type_decl) :
    string =
  let type_decl_id_to_string (id : T.TypeDeclId.id) : string =
    let decl = T.TypeDeclId.Map.find id type_context in
    name_to_string decl.name
  in
  let global_decl_id_to_string def_id =
    let def = GA.GlobalDeclId.Map.find def_id global_context in
    get_global_decl_name_as_string def
  in
  PT.type_decl_to_string type_decl_id_to_string global_decl_id_to_string decl

(** Generate an [ast_formatter] by using a declaration context and some additional
    parameters *)
let decl_ctx_to_ast_formatter (type_context : T.type_decl T.TypeDeclId.Map.t)
    (fun_context : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_context : 'global_decl GA.GlobalDeclId.Map.t)
    (region_vars : T.region_var list) (type_params : T.type_var list)
    (const_generic_params : T.const_generic_var list) (locals : GA.var list)
    (get_global_decl_name_as_string : 'gdecl -> string) : ast_formatter =
  let rvar_to_string vid =
    let var = T.RegionVarId.nth region_vars vid in
    PT.region_var_to_string var
  in
  let r_to_string vid =
    (* TODO: we might want something more informative *)
    PT.region_id_to_string vid
  in
  let type_var_id_to_string vid =
    let var = T.TypeVarId.nth type_params vid in
    PT.type_var_to_string var
  in
  let const_generic_var_id_to_string vid =
    let var = T.ConstGenericVarId.nth const_generic_params vid in
    PT.const_generic_var_to_string var
  in
  let type_decl_id_to_string def_id =
    let def = T.TypeDeclId.Map.find def_id type_context in
    name_to_string def.name
  in
  let fun_decl_id_to_string def_id =
    let def = GA.FunDeclId.Map.find def_id fun_context in
    fun_name_to_string def.name
  in
  let global_decl_id_to_string def_id =
    let def = GA.GlobalDeclId.Map.find def_id global_context in
    get_global_decl_name_as_string def
  in
  let var_id_to_string vid =
    let var = E.VarId.nth locals vid in
    var_to_string var
  in
  let adt_variant_to_string =
    PT.type_ctx_to_adt_variant_to_string_fun type_context
  in
  let adt_field_to_string =
    PT.type_ctx_to_adt_field_to_string_fun type_context
  in
  let adt_field_names = PT.type_ctx_to_adt_field_names_fun type_context in
  {
    rvar_to_string;
    r_to_string;
    type_var_id_to_string;
    type_decl_id_to_string;
    const_generic_var_id_to_string;
    adt_variant_to_string;
    adt_field_to_string;
    var_id_to_string;
    adt_field_names;
    fun_decl_id_to_string;
    global_decl_id_to_string;
  }

(** Generate an [ast_formatter] by using a declaration context in combination
    with the variables local to a function's declaration *)
let decl_ctx_and_fun_decl_to_ast_formatter
    (type_context : T.type_decl T.TypeDeclId.Map.t)
    (fun_context : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_context : 'global_decl GA.GlobalDeclId.Map.t)
    (get_global_decl_name_as_string : 'gdecl -> string)
    (def : 'body GA.gfun_decl) : ast_formatter =
  let region_vars = def.signature.region_params in
  let type_params = def.signature.type_params in
  let cg_params = def.signature.const_generic_params in
  let locals = match def.body with None -> [] | Some body -> body.locals in
  decl_ctx_to_ast_formatter type_context fun_context global_context region_vars
    type_params cg_params locals get_global_decl_name_as_string
