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

(** Generate an [ast_formatter] by using a declaration context and some additional
    parameters *)
let gdecls_to_ast_formatter (type_decls : T.type_decl T.TypeDeclId.Map.t)
    (fun_decls : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_decls : 'gdecl GA.GlobalDeclId.Map.t)
    (trait_decls : GA.trait_decl GA.TraitDeclId.Map.t)
    (trait_impls : GA.trait_impl GA.TraitImplId.Map.t)
    (generics : T.generic_params) (locals : GA.var list option)
    (get_global_decl_name_as_string : 'gdecl -> string) : ast_formatter =
  let rvar_to_string r =
    let rvar = T.RegionVarId.nth generics.regions r in
    PT.region_var_to_string rvar
  in
  let r_to_string r =
    (* TODO: we might want something more informative *)
    PT.region_id_to_string r
  in

  let type_var_id_to_string vid =
    let var = T.TypeVarId.nth generics.types vid in
    PT.type_var_to_string var
  in
  let const_generic_var_id_to_string vid =
    let var = T.ConstGenericVarId.nth generics.const_generics vid in
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
    let var = E.VarId.nth (Option.get locals) vid in
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
  let trait_decl_id_to_string id =
    let def = GA.TraitDeclId.Map.find id trait_decls in
    name_to_string def.name
  in
  let trait_impl_id_to_string id =
    let def = GA.TraitImplId.Map.find id trait_impls in
    name_to_string def.name
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
    trait_decl_id_to_string;
    trait_impl_id_to_string;
    trait_clause_id_to_string = PT.trait_clause_id_to_pretty_string;
  }

let gdecls_and_gfun_decl_to_ast_formatter
    (type_decls : T.type_decl T.TypeDeclId.Map.t)
    (fun_decls : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_decls : 'gdecl GA.GlobalDeclId.Map.t)
    (trait_decls : GA.trait_decl GA.TraitDeclId.Map.t)
    (trait_impls : GA.trait_impl GA.TraitImplId.Map.t)
    (get_global_decl_name_as_string : 'gdecl -> string)
    (fdef : 'body GA.gfun_decl) : ast_formatter =
  let locals =
    match fdef.body with None -> None | Some body -> Some body.locals
  in
  gdecls_to_ast_formatter type_decls fun_decls global_decls trait_decls
    trait_impls fdef.signature.generics locals get_global_decl_name_as_string

let call_to_string (fmt : ast_formatter) (indent : string) (call : GA.call) :
    string =
  let ty_fmt = ast_to_etype_formatter fmt in
  let generics = PT.generic_args_to_string ty_fmt call.GA.generics in
  let args = List.map (PE.operand_to_string fmt) call.GA.args in
  let args = "(" ^ String.concat ", " args ^ ")" in
  let name_args =
    match call.GA.func with
    | GA.TraitMethod (trait_ref, method_name) ->
        let fmt = ast_to_etype_formatter fmt in
        PT.trait_ref_to_string fmt trait_ref ^ "::" ^ method_name ^ generics
    | GA.FunId (GA.Regular fid) -> fmt.fun_decl_id_to_string fid ^ generics
    | GA.FunId (GA.Assumed fid) -> (
        match fid with
        | GA.Replace -> "core::mem::replace" ^ generics
        | GA.BoxNew -> "alloc::boxed::Box" ^ generics ^ "::new"
        | GA.BoxDeref -> "core::ops::deref::Deref<Box" ^ generics ^ ">::deref"
        | GA.BoxDerefMut ->
            "core::ops::deref::DerefMut" ^ generics ^ "::deref_mut"
        | GA.BoxFree -> "alloc::alloc::box_free" ^ generics
        | GA.VecNew -> "alloc::vec::Vec" ^ generics ^ "::new"
        | GA.VecPush -> "alloc::vec::Vec" ^ generics ^ "::push"
        | GA.VecInsert -> "alloc::vec::Vec" ^ generics ^ "::insert"
        | GA.VecLen -> "alloc::vec::Vec" ^ generics ^ "::len"
        | GA.VecIndex ->
            "core::ops::index::Index<alloc::vec::Vec" ^ generics ^ ">::index"
        | GA.VecIndexMut ->
            "core::ops::index::IndexMut<alloc::vec::Vec" ^ generics
            ^ ">::index_mut"
        | GA.ArrayIndexShared -> "@ArrayIndexShared" ^ generics
        | GA.ArrayIndexMut -> "@ArrayIndexMut" ^ generics
        | GA.ArrayToSliceShared -> "@ArrayToSliceShared" ^ generics
        | GA.ArrayToSliceMut -> "@ArrayToSliceMut" ^ generics
        | GA.ArraySubsliceShared -> "@ArraySubsliceShared" ^ generics
        | GA.ArraySubsliceMut -> "@ArraySubsliceMut" ^ generics
        | GA.SliceLen -> "@SliceLen" ^ generics
        | GA.SliceIndexShared -> "@SliceIndexShared" ^ generics
        | GA.SliceIndexMut -> "@SliceIndexMut" ^ generics
        | GA.SliceSubsliceShared -> "@SliceSubsliceShared" ^ generics
        | GA.SliceSubsliceMut -> "@SliceSubsliceMut" ^ generics)
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

  (* Generics and predicates *)
  let params, trait_clauses =
    PT.generic_params_to_strings sty_fmt sg.generics
  in
  let clauses =
    PT.predicates_and_trait_clauses_to_string sty_fmt indent indent_incr
      sg.parent_params_info trait_clauses sg.preds
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
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
      ^ clauses
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
      indent ^ "fn " ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty ^ clauses
      ^ "\n{\n" ^ locals ^ "\n\n" ^ body ^ "\n" ^ indent ^ "}"

let trait_decl_to_string (fmt : ast_formatter) (indent : string)
    (indent_incr : string) (def : GA.trait_decl) : string =
  let sty_fmt = ast_to_stype_formatter fmt in
  let ety_fmt = ast_to_etype_formatter fmt in
  let ety_to_string = PT.ety_to_string ety_fmt in

  (* Name *)
  let name = name_to_string def.GA.name in

  (* Generics and predicates *)
  let params, trait_clauses =
    PT.generic_params_to_strings sty_fmt def.generics
  in
  let clauses =
    PT.predicates_and_trait_clauses_to_string sty_fmt indent indent_incr None
      trait_clauses def.preds
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in

  let items =
    let consts =
      List.map
        (fun (name, (ty, opt_id)) ->
          let ty = ety_to_string ty in
          let lhs = indent ^ "const " ^ name ^ " : " ^ ty in
          match opt_id with
          | None -> lhs ^ "\n"
          | Some id -> lhs ^ " = " ^ fmt.global_decl_id_to_string id ^ "\n")
        def.consts
    in
    let types =
      List.map
        (fun (name, (clauses, opt_ty)) ->
          let clauses = List.map (PT.trait_clause_to_string sty_fmt) clauses in
          let clauses = PT.clauses_to_string indent indent_incr 0 clauses in
          match opt_ty with
          | None -> indent ^ "type " ^ name ^ clauses ^ "\n"
          | Some ty ->
              indent ^ "type " ^ name ^ " = " ^ ety_to_string ty ^ clauses
              ^ "\n")
        def.types
    in
    let required_methods =
      List.map
        (fun (name, f) ->
          indent ^ "fn " ^ name ^ " : " ^ fmt.fun_decl_id_to_string f ^ "\n")
        def.required_methods
    in
    let provided_methods =
      List.map (fun name -> indent ^ "fn " ^ name ^ "\n") def.provided_methods
    in
    let items =
      List.concat [ consts; types; required_methods; provided_methods ]
    in
    if items = [] then "" else "\n{\n" ^ String.concat "" items ^ "}"
  in

  "trait " ^ name ^ params ^ clauses ^ items

let impl_trait_ref_to_string (fmt : ast_formatter)
    (impl_trait : GA.impl_trait_ref) : string =
  let sty_fmt = ast_to_stype_formatter fmt in
  let trait_id = fmt.trait_decl_id_to_string impl_trait.GA.trait_id in
  let generics = PT.generic_args_to_string sty_fmt impl_trait.GA.generics in
  trait_id ^ generics

let trait_impl_to_string (fmt : ast_formatter) (indent : string)
    (indent_incr : string) (def : GA.trait_impl) : string =
  let sty_fmt = ast_to_stype_formatter fmt in
  let ety_fmt = ast_to_etype_formatter fmt in
  let ety_to_string = PT.ety_to_string ety_fmt in

  (* Name *)
  let name = name_to_string def.GA.name in

  (* Generics and predicates *)
  let params, trait_clauses =
    PT.generic_params_to_strings sty_fmt def.generics
  in
  let clauses =
    PT.predicates_and_trait_clauses_to_string sty_fmt indent indent_incr None
      trait_clauses def.preds
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in

  let items =
    let consts =
      List.map
        (fun (name, (ty, id)) ->
          let ty = ety_to_string ty in
          let id = fmt.global_decl_id_to_string id in
          indent ^ "const " ^ name ^ " : " ^ ty ^ " = " ^ id ^ "\n")
        def.consts
    in
    let types =
      List.map
        (fun (name, ty) ->
          indent ^ "type " ^ name ^ " = " ^ ety_to_string ty ^ "\n")
        def.types
    in
    let methods =
      List.map
        (fun (name, f) ->
          indent ^ "fn " ^ name ^ " : " ^ fmt.fun_decl_id_to_string f ^ "\n")
        (List.append def.required_methods def.provided_methods)
    in
    let items = List.concat [ consts; types; methods ] in
    if items = [] then "" else "\n{\n" ^ String.concat "" items ^ "}"
  in

  let impl_trait = impl_trait_ref_to_string fmt def.impl_trait in
  "impl" ^ params ^ " " ^ name ^ params ^ " : " ^ impl_trait ^ clauses ^ items

(** This function pretty-prints a type definition by using a definition context *)
let ctx_and_type_decl_to_string (type_context : T.type_decl T.TypeDeclId.Map.t)
    (global_context : 'global_decl GA.GlobalDeclId.Map.t)
    (trait_decls_context : GA.trait_decl GA.TraitDeclId.Map.t)
    (trait_impls_context : GA.trait_impl GA.TraitImplId.Map.t)
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
  let trait_decl_id_to_string def_id =
    let def = GA.TraitDeclId.Map.find def_id trait_decls_context in
    name_to_string def.name
  in
  let trait_impl_id_to_string def_id =
    let def = GA.TraitImplId.Map.find def_id trait_impls_context in
    name_to_string def.name
  in
  PT.type_decl_to_string type_decl_id_to_string global_decl_id_to_string
    trait_decl_id_to_string trait_impl_id_to_string decl

(** Generate an [ast_formatter] by using a declaration context in combination
    with the variables local to a function declaration *)
let decl_ctx_and_fun_decl_to_ast_formatter
    (type_context : T.type_decl T.TypeDeclId.Map.t)
    (fun_context : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_context : 'global_decl GA.GlobalDeclId.Map.t)
    (trait_decls_context : GA.trait_decl GA.TraitDeclId.Map.t)
    (trait_impls_context : GA.trait_impl GA.TraitImplId.Map.t)
    (get_global_decl_name_as_string : 'gdecl -> string)
    (def : 'body GA.gfun_decl) : ast_formatter =
  let locals =
    match def.body with None -> None | Some body -> Some body.locals
  in
  gdecls_to_ast_formatter type_context fun_context global_context
    trait_decls_context trait_impls_context def.signature.generics locals
    get_global_decl_name_as_string

(** Generate an [ast_formatter] by using a declaration context in combination
    with the variables local to a trait declaration *)
let decl_ctx_and_trait_decl_to_ast_formatter
    (type_context : T.type_decl T.TypeDeclId.Map.t)
    (fun_context : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_context : 'global_decl GA.GlobalDeclId.Map.t)
    (trait_decls_context : GA.trait_decl GA.TraitDeclId.Map.t)
    (trait_impls_context : GA.trait_impl GA.TraitImplId.Map.t)
    (get_global_decl_name_as_string : 'gdecl -> string) (def : GA.trait_decl) :
    ast_formatter =
  let locals = None in
  gdecls_to_ast_formatter type_context fun_context global_context
    trait_decls_context trait_impls_context def.generics locals
    get_global_decl_name_as_string

(** Generate an [ast_formatter] by using a declaration context in combination
    with the variables local to a trait implementation *)
let decl_ctx_and_trait_impl_to_ast_formatter
    (type_context : T.type_decl T.TypeDeclId.Map.t)
    (fun_context : 'body GA.gfun_decl GA.FunDeclId.Map.t)
    (global_context : 'global_decl GA.GlobalDeclId.Map.t)
    (trait_decls_context : GA.trait_decl GA.TraitDeclId.Map.t)
    (trait_impls_context : GA.trait_impl GA.TraitImplId.Map.t)
    (get_global_decl_name_as_string : 'gdecl -> string) (def : GA.trait_impl) :
    ast_formatter =
  let locals = None in
  gdecls_to_ast_formatter type_context fun_context global_context
    trait_decls_context trait_impls_context def.generics locals
    get_global_decl_name_as_string
