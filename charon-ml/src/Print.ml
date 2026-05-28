(** Compatibility string API for pretty-printing.

    Formatter implementations live in [PrintFmt] so opening [Print] only brings
    the legacy string conversion API into scope. *)

open Types
open GAst

type fmt_env = PrintFmt.fmt_env

let integer_type_to_string ty =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_integer_type fmt ty)

let float_type_to_string ty =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_float_type fmt ty)

let literal_type_to_string ty =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_literal_type fmt ty)

let big_int_to_string bi =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_big_int fmt bi)

let scalar_value_to_string sv =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_scalar_value fmt sv)

let float_value_to_string fv =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_float_value fmt fv)

let literal_to_string lit =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_literal fmt lit)

let g_region_group_to_string rid_to_string id_to_string gr =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_g_region_group
        (fun fmt rid -> Format.pp_print_string fmt (rid_to_string rid))
        (fun fmt id -> Format.pp_print_string fmt (id_to_string id))
        fmt gr)

let region_var_group_to_string gr =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_region_var_group fmt gr)

let region_var_groups_to_string gl =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_region_var_groups fmt gl)

let ref_kind_to_string rk =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_ref_kind fmt rk)

let builtin_ty_to_string _ = "Box"

let de_bruijn_var_to_pretty_string show_varid var =
  PrintFmt.de_bruijn_var_to_pretty_string show_varid var

let region_db_var_to_pretty_string var =
  PrintFmt.region_db_var_to_pretty_string var

let type_db_var_to_pretty_string var = PrintFmt.type_db_var_to_pretty_string var
let type_var_id_to_pretty_string id = PrintFmt.type_var_id_to_pretty_string id
let type_param_to_string tv = PrintFmt.type_param_to_string tv

let const_generic_var_id_to_pretty_string id =
  PrintFmt.const_generic_var_id_to_pretty_string id

let const_generic_db_var_to_pretty_string var =
  PrintFmt.const_generic_db_var_to_pretty_string var

let const_generic_param_to_string ty_to_string v =
  PrintFmt.const_generic_param_to_string ty_to_string v

let trait_clause_id_to_pretty_string id =
  PrintFmt.trait_clause_id_to_pretty_string id

let trait_db_var_to_pretty_string var =
  PrintFmt.trait_db_var_to_pretty_string var

let type_decl_id_to_pretty_string id = PrintFmt.type_decl_id_to_pretty_string id
let fun_decl_id_to_pretty_string id = PrintFmt.fun_decl_id_to_pretty_string id

let global_decl_id_to_pretty_string id =
  PrintFmt.global_decl_id_to_pretty_string id

let trait_decl_id_to_pretty_string id =
  PrintFmt.trait_decl_id_to_pretty_string id

let trait_impl_id_to_pretty_string id =
  PrintFmt.trait_impl_id_to_pretty_string id

let variant_id_to_pretty_string id = PrintFmt.variant_id_to_pretty_string id
let field_id_to_pretty_string id = PrintFmt.field_id_to_pretty_string id
let item_id_to_pretty_string id = PrintFmt.item_id_to_pretty_string id

let region_param_to_string_at_depth binder_depth rv =
  PrintFmt.region_param_to_string_at_depth binder_depth rv

let region_param_to_string env rv = PrintFmt.region_param_to_string env rv

let anonymous_region_param_to_string env var r =
  PrintFmt.anonymous_region_param_to_string env var r

let trait_clause_id_to_string_with_suffix level_suffix id =
  PrintFmt.trait_clause_id_to_string_with_suffix level_suffix id

let trait_clause_id_to_string_for_env env id =
  PrintFmt.trait_clause_id_to_string_for_env env id

let trait_clause_id_to_string _ id =
  PrintFmt.trait_clause_id_to_pretty_string id

let trait_clause_var_to_string env var =
  PrintFmt.trait_clause_var_to_string env var

let region_db_var_to_string env var = PrintFmt.region_db_var_to_string env var
let type_db_var_to_string env var = PrintFmt.type_db_var_to_string env var

let const_generic_db_var_to_string env var =
  PrintFmt.const_generic_db_var_to_string env var

let trait_db_var_to_string env var = PrintFmt.trait_db_var_to_string env var
let region_to_string env r = PrintFmt.region_to_string env r

let region_binder_to_string value_to_string env rb =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_region_binder
        (fun env fmt value ->
          Format.pp_print_string fmt (value_to_string env value))
        env fmt rb)

let type_id_to_string env id =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_type_id env fmt id)

let type_decl_id_to_string env def_id =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_type_decl_id env fmt def_id)

let type_decl_ref_to_string env tref =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_type_decl_ref env fmt tref)

let fun_decl_id_to_string env id =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_fun_decl_id env fmt id)

let fun_decl_ref_to_string env fn =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_fun_decl_ref env fmt fn)

let global_decl_id_to_string env def_id =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_global_decl_id env fmt def_id)

let global_decl_ref_to_string env gr =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_global_decl_ref env fmt gr)

let trait_decl_id_to_string env id =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_trait_decl_id env fmt id)

let trait_impl_id_to_string env id =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_trait_impl_id env fmt id)

let trait_impl_ref_to_string env iref =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_trait_impl_ref env fmt iref)

let provenance_to_string env pv =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_provenance env fmt pv)

let byte_to_string env cv =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_byte env fmt cv)

let unsizing_metadata_to_string env meta =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_unsizing_metadata env fmt meta)

let const_aggregate_to_string env tref opt_variant_id fields =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_const_aggregate env tref opt_variant_id fmt fields)

let constant_expr_to_string env cv =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_constant_expr env fmt cv)

let builtin_fun_id_to_string aid =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_builtin_fun_id fmt aid)

let fun_id_to_string env fid =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_fun_id env fmt fid)

let fn_ptr_kind_to_string env kind =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_fn_ptr_kind env fmt kind)

let fn_ptr_to_string env ptr =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_fn_ptr env fmt ptr)

let ty_to_string env ty =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_ty env fmt ty)

let dyn_trait_type_constraint_to_string env ttc =
  PrintFmt.dyn_trait_type_constraint_to_string env ttc

let dyn_trait_clause_to_string env constraints clause =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_dyn_trait_clause env constraints clause fmt)

let dyn_types_outlive_to_string env rb =
  PrintFmt.dyn_types_outlive_to_string env rb

let dyn_predicate_to_string env pred =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_dyn_predicate env fmt pred)

let generic_args_to_strings env generics =
  PrintFmt.generic_args_to_strings env generics

let generic_args_to_string env generics =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_generic_args env fmt generics)

let generic_args_to_string_for_fn env generics =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_generic_args_for_fn env fmt generics)

let trait_ref_kind_to_string env implements kind =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_trait_ref_kind env implements fmt kind)

let trait_ref_to_string env tr =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_trait_ref env fmt tr)

let trait_decl_ref_to_string env tr =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_trait_decl_ref env fmt tr)

let trait_decl_ref_as_impl_to_string env tr =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_trait_decl_ref_as_impl env fmt tr)

let impl_elem_to_string env elem =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_impl_elem env fmt elem)

let path_elem_to_string env elem =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_path_elem env fmt elem)

let name_to_string env name =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_name env fmt name)

let raw_attribute_to_string attr =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_raw_attribute fmt attr)

let trait_param_to_string env clause =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_trait_param env fmt clause)

let generic_params_to_strings env generics =
  PrintFmt.generic_params_to_strings env generics

let adt_variant_to_string env def_id variant_id =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_adt_variant env def_id fmt variant_id)

let adt_field_names env def_id opt_variant_id =
  PrintFmt.adt_field_names env def_id opt_variant_id

let field_to_string env f =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_field env fmt f)

let variant_to_string env v =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_variant env fmt v)

let trait_type_constraint_to_string env ttc =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_trait_type_constraint env fmt ttc)

let clauses_to_string indent indent_incr clauses =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_clauses indent indent_incr fmt clauses)

let predicates_and_trait_clauses_to_string env indent indent_incr generics =
  PrintFmt.predicates_and_trait_clauses_to_string env indent indent_incr
    generics

let generic_params_to_string_single_line env generics =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_generic_params_single_line env fmt generics)

let item_intro_to_string env indent keyword id meta =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_item_intro env indent keyword id fmt meta)

let type_decl_to_string env def =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_type_decl env fmt def)

let adt_field_to_string env def_id opt_variant_id field_id =
  PrintFmt.adt_field_to_string env def_id opt_variant_id field_id

let local_id_to_pretty_string id = PrintFmt.local_id_to_pretty_string id
let local_to_string v = PrintFmt.local_to_string v
let local_id_to_string env id = PrintFmt.local_id_to_string env id

let (var_id_to_pretty_string
     [@ocaml.alert deprecated "use [local_id_to_pretty_string] instead"]) =
  local_id_to_pretty_string

let (var_id_to_string
     [@ocaml.alert deprecated "use [local_id_to_string] instead"]) =
  local_id_to_string

let (var_to_string [@ocaml.alert deprecated "use [local_to_string] instead"]) =
  local_to_string

let projection_elem_to_string env sub pe =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_projection_elem env sub fmt pe)

let place_to_string env p =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_place env fmt p)

let cast_kind_to_string env cast =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_cast_kind env fmt cast)

let nullop_to_string env op =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_nullop env fmt op)

let unop_to_string env unop =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_unop env fmt unop)

let overflow_mode_to_string mode =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_overflow_mode fmt mode)

let binop_to_string binop =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_binop fmt binop)

let operand_to_string env op =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_operand env fmt op)

let aggregate_to_string env agg fields =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_aggregate env agg fmt fields)

let rvalue_to_string env rv =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_rvalue env fmt rv)

let item_id_to_string (id : item_id) : string =
  match id with
  | IdFun id -> FunDeclId.to_string id
  | IdGlobal id -> GlobalDeclId.to_string id
  | IdType id -> TypeDeclId.to_string id
  | IdTraitDecl id -> TraitDeclId.to_string id
  | IdTraitImpl id -> TraitImplId.to_string id

let fn_operand_to_string env op =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_fn_operand env fmt op)

let call_to_string env indent call =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_call env indent fmt call)

let assertion_to_string env a =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_assertion env fmt a)

let abort_kind_to_string env a =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_abort_kind env fmt a)

let fun_sig_with_name_to_string env indent indent_incr attribute name args sg =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_fun_sig_with_name env indent indent_incr attribute name args
        fmt sg)

let fun_sig_to_string env indent indent_incr sg =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_fun_sig env indent indent_incr fmt sg)

let locals_to_string env indent locals =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_locals env indent fmt locals)

let trait_decl_to_string env indent indent_incr def =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_trait_decl env indent indent_incr fmt def)

let trait_impl_to_string env indent indent_incr def =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_trait_impl env indent indent_incr fmt def)

let global_decl_to_string env indent indent_incr def =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_global_decl env indent indent_incr fmt def)

let fun_decl_to_string env indent indent_incr def =
  PrintFmt.pp_to_string (fun fmt ->
      PrintFmt.pp_fun_decl env indent indent_incr fmt def)

let crate_to_fmt_env crate = PrintFmt.crate_to_fmt_env crate

let crate_to_string m =
  PrintFmt.pp_to_string (fun fmt -> PrintFmt.pp_crate fmt m)

module Llbc = struct
  let statement_to_string env indent indent_incr st =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Llbc.pp_statement env indent indent_incr fmt st)

  let statement_kind_to_string env indent indent_incr st =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Llbc.pp_statement_kind env indent indent_incr fmt st)

  let block_to_string env indent indent_incr b =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Llbc.pp_block env indent indent_incr fmt b)
end

module Ullbc = struct
  let statement_to_string env indent st =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Ullbc.pp_statement env indent fmt st)

  let statement_kind_to_string env indent st =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Ullbc.pp_statement_kind env indent fmt st)

  let switch_to_string indent tgt =
    PrintFmt.pp_to_string (fun fmt -> PrintFmt.Ullbc.pp_switch indent fmt tgt)

  let terminator_to_string env indent st =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Ullbc.pp_terminator env indent fmt st)

  let terminator_kind_to_string env indent st =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Ullbc.pp_terminator_kind env indent fmt st)

  let block_to_string env indent indent_incr id block =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Ullbc.pp_block env indent indent_incr fmt id block)

  let blocks_to_string env indent indent_incr blocks =
    PrintFmt.pp_to_string (fun fmt ->
        PrintFmt.Ullbc.pp_blocks env indent indent_incr fmt blocks)
end
