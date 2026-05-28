(** Pretty-printing for types *)

open Values
open Meta
open Types
open Expressions
open GAst
open TypesUtils
open GAstUtils
open PrintUtils

type fmt_env = PrintUtils.fmt_env

let pp_string = Format.pp_print_string

let pp_to_string (pp : Format.formatter -> unit) : string =
  let buf = Buffer.create 4096 in
  let fmt = Format.formatter_of_buffer buf in
  pp fmt;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let pp_sep_list (sep : string) (pp : Format.formatter -> 'a -> unit)
    (fmt : Format.formatter) (xs : 'a list) : unit =
  let rec loop = function
    | [] -> ()
    | [ x ] -> pp fmt x
    | x :: xs ->
        pp fmt x;
        pp_string fmt sep;
        loop xs
  in
  loop xs

let pp_integer_type (fmt : Format.formatter) = function
  | Signed Isize -> pp_string fmt "isize"
  | Signed I8 -> pp_string fmt "i8"
  | Signed I16 -> pp_string fmt "i16"
  | Signed I32 -> pp_string fmt "i32"
  | Signed I64 -> pp_string fmt "i64"
  | Signed I128 -> pp_string fmt "i128"
  | Unsigned Usize -> pp_string fmt "usize"
  | Unsigned U8 -> pp_string fmt "u8"
  | Unsigned U16 -> pp_string fmt "u16"
  | Unsigned U32 -> pp_string fmt "u32"
  | Unsigned U64 -> pp_string fmt "u64"
  | Unsigned U128 -> pp_string fmt "u128"

let pp_float_type (fmt : Format.formatter) = function
  | F16 -> pp_string fmt "f16"
  | F32 -> pp_string fmt "f32"
  | F64 -> pp_string fmt "f64"
  | F128 -> pp_string fmt "f128"

let pp_literal_type (fmt : Format.formatter) (ty : literal_type) : unit =
  match ty with
  | TInt ity -> pp_integer_type fmt (Signed ity)
  | TUInt uty -> pp_integer_type fmt (Unsigned uty)
  | TFloat fty -> pp_float_type fmt fty
  | TBool -> pp_string fmt "bool"
  | TChar -> pp_string fmt "char"

let pp_big_int (fmt : Format.formatter) (bi : big_int) : unit =
  pp_string fmt (Z.to_string bi)

let pp_scalar_value (fmt : Format.formatter) (sv : scalar_value) : unit =
  Format.fprintf fmt "%a : %a" pp_big_int (Scalars.get_val sv) pp_integer_type
    (Scalars.get_ty sv)

let pp_float_value (fmt : Format.formatter) (fv : float_value) : unit =
  Format.fprintf fmt "%s : %a" fv.float_value pp_float_type fv.float_ty

let escape_string (s : string) : string =
  let buf = Buffer.create (String.length s) in
  String.iter
    (function
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\n' -> Buffer.add_string buf "\\n"
      | c -> Buffer.add_char buf c)
    s;
  Buffer.contents buf

let uchar_to_utf8 (c : Uchar.t) : string =
  let i = Uchar.to_int c in
  let byte n = Char.chr (n land 0xff) in
  let cont n = byte (0x80 lor (n land 0x3f)) in
  if i <= 0x7f then String.make 1 (byte i)
  else if i <= 0x7ff then
    String.init 2 (function
      | 0 -> byte (0xc0 lor ((i lsr 6) land 0x1f))
      | _ -> cont i)
  else if i <= 0xffff then
    String.init 3 (function
      | 0 -> byte (0xe0 lor ((i lsr 12) land 0x0f))
      | 1 -> cont (i lsr 6)
      | _ -> cont i)
  else
    String.init 4 (function
      | 0 -> byte (0xf0 lor ((i lsr 18) land 0x07))
      | 1 -> cont (i lsr 12)
      | 2 -> cont (i lsr 6)
      | _ -> cont i)

let pp_literal (fmt : Format.formatter) (lit : literal) : unit =
  match lit with
  | VScalar sv -> pp_scalar_value fmt sv
  | VFloat fv -> pp_float_value fmt fv
  | VBool b -> pp_string fmt (Bool.to_string b)
  | VChar c -> pp_string fmt (uchar_to_utf8 c)
  | VStr s -> Format.fprintf fmt "\"%s\"" (escape_string s)
  | VByteStr bs ->
      Format.fprintf fmt "[%a]"
        (pp_sep_list ", " (fun fmt b -> pp_string fmt (string_of_int b)))
        bs

let pp_g_region_group (pp_rid : Format.formatter -> 'rid -> unit)
    (pp_id : Format.formatter -> 'id -> unit) (fmt : Format.formatter)
    (gr : ('rid, 'id) g_region_group) : unit =
  let { id; regions; parents } = gr in
  Format.fprintf fmt "{ id: %a; regions: [%a]; parents: [%a] }" pp_id id
    (pp_sep_list ", " pp_rid) regions (pp_sep_list ", " pp_id) parents

let pp_region_var_group (fmt : Format.formatter) (gr : region_var_group) : unit
    =
  pp_g_region_group
    (fun fmt rid -> pp_string fmt (RegionId.to_string rid))
    (fun fmt id -> pp_string fmt (RegionGroupId.to_string id))
    fmt gr

let pp_region_var_groups (fmt : Format.formatter) (gl : region_var_groups) :
    unit =
  pp_sep_list "\n" pp_region_var_group fmt gl

let pp_ref_kind (fmt : Format.formatter) (rk : ref_kind) : unit =
  match rk with
  | RMut -> pp_string fmt "Mut"
  | RShared -> pp_string fmt "Shared"

let de_bruijn_var_to_pretty_string show_varid var : string =
  match var with
  | Bound (dbid, varid) -> show_de_bruijn_id dbid ^ "_" ^ show_varid varid
  | Free varid -> show_varid varid

let region_db_var_to_pretty_string (var : region_db_var) : string =
  "'" ^ de_bruijn_var_to_pretty_string RegionId.to_string var

let type_db_var_to_pretty_string (var : type_db_var) : string =
  "@Type" ^ de_bruijn_var_to_pretty_string TypeVarId.to_string var

let type_var_id_to_pretty_string (id : type_var_id) : string =
  "@Type" ^ TypeVarId.to_string id

let type_param_to_string (tv : type_param) : string = tv.name

let const_generic_var_id_to_pretty_string (id : const_generic_var_id) : string =
  "@ConstGeneric" ^ ConstGenericVarId.to_string id

let const_generic_db_var_to_pretty_string (var : const_generic_db_var) : string
    =
  "@ConstGeneric"
  ^ de_bruijn_var_to_pretty_string ConstGenericVarId.to_string var

let const_generic_param_to_string (ty_to_string : ty -> string)
    (v : const_generic_param) : string =
  "const " ^ v.name ^ " : " ^ ty_to_string v.ty

let trait_clause_id_to_pretty_string (id : trait_clause_id) : string =
  "@TraitClause" ^ TraitClauseId.to_string id

let trait_db_var_to_pretty_string (var : trait_db_var) : string =
  "@TraitClause" ^ de_bruijn_var_to_pretty_string TraitClauseId.to_string var

let type_decl_id_to_pretty_string (id : type_decl_id) : string =
  "TypeDecl@" ^ TypeDeclId.to_string id

let fun_decl_id_to_pretty_string (id : FunDeclId.id) : string =
  "FunDecl@" ^ FunDeclId.to_string id

let global_decl_id_to_pretty_string (id : GlobalDeclId.id) : string =
  "GlobalDecl@" ^ GlobalDeclId.to_string id

let trait_decl_id_to_pretty_string (id : trait_decl_id) : string =
  "TraitDecl@" ^ TraitDeclId.to_string id

let trait_impl_id_to_pretty_string (id : trait_impl_id) : string =
  "TraitImpl@" ^ TraitImplId.to_string id

let variant_id_to_pretty_string (id : variant_id) : string =
  "Variant@" ^ VariantId.to_string id

let field_id_to_pretty_string (id : field_id) : string =
  "Field@" ^ FieldId.to_string id

let tab_incr = "    "

type 'id de_bruijn_var_location = { dbid : int; varid : 'id }

let binding_level_suffix (level : int) : string =
  if level <= 0 then "" else "_" ^ string_of_int level

let current_binding_level_suffix (env : fmt_env) : string =
  binding_level_suffix (List.length env.generics - 1)

let de_bruijn_var_location (env : fmt_env) (var : 'id de_bruijn_var) :
    'id de_bruijn_var_location option =
  if List.length env.generics = 0 then None
  else
    let dbid, varid =
      match var with
      | Bound (dbid, varid) -> (dbid, varid)
      | Free varid -> (List.length env.generics - 1, varid)
    in
    Some { dbid; varid }

let de_bruijn_var_binding_level_suffix (env : fmt_env) (var : 'id de_bruijn_var)
    : string =
  match de_bruijn_var_location env var with
  | None -> ""
  | Some { dbid; _ } ->
      binding_level_suffix (List.length env.generics - 1 - dbid)

let generic_params_at_dbid (env : fmt_env) (dbid : int) : generic_params option
    =
  match List.nth_opt env.generics dbid with
  | Some generics -> Some generics
  | None ->
      let index = List.length env.generics - dbid in
      if dbid > 0 && index >= 0 then List.nth_opt env.generics index else None

let find_short_name (env : fmt_env) (id : item_id) : name option =
  match List.assoc_opt id env.crate.short_names with
  | Some name -> Some name
  | None -> List.assoc_opt id env.crate.item_names

let has_short_name (env : fmt_env) (id : item_id) : name option =
  List.assoc_opt id env.crate.short_names

let item_id_to_pretty_string (id : item_id) : string =
  match id with
  | IdType id -> type_decl_id_to_pretty_string id
  | IdFun id -> fun_decl_id_to_pretty_string id
  | IdGlobal id -> global_decl_id_to_pretty_string id
  | IdTraitDecl id -> trait_decl_id_to_pretty_string id
  | IdTraitImpl id -> trait_impl_id_to_pretty_string id

let lookup_var_in_env (env : fmt_env)
    (find_in : generic_params -> 'id -> 'b option) (var : 'id de_bruijn_var) :
    'b option =
  match de_bruijn_var_location env var with
  | None -> None
  | Some { dbid; varid } -> (
      match generic_params_at_dbid env dbid with
      | None -> None
      | Some generics -> (
          match find_in generics varid with
          | None -> None
          | Some r -> Some r))

let region_param_to_string_at_depth (binder_depth : int) (rv : region_param) :
    string =
  let mutability =
    match rv.mutability with
    | LtMutable -> "mut "
    | LtShared | LtUnknown -> ""
  in
  match rv.name with
  | Some name -> mutability ^ name
  | None ->
      let depth = binding_level_suffix (binder_depth - 1) in
      mutability ^ "'_" ^ RegionId.to_string rv.index ^ depth

let region_param_to_string (env : fmt_env) (rv : region_param) : string =
  region_param_to_string_at_depth (List.length env.generics) rv

let lookup_region_param (env : fmt_env) (var : region_db_var) :
    region_param option =
  (* Note that the regions are not necessarily ordered following their indices *)
  let find (generics : generic_params) varid =
    List.find_opt (fun (v : region_param) -> v.index = varid) generics.regions
  in
  lookup_var_in_env env find var

let anonymous_region_param_to_string (env : fmt_env) (var : region_db_var)
    (r : region_param) : string =
  "'_" ^ RegionId.to_string r.index ^ de_bruijn_var_binding_level_suffix env var

let trait_clause_id_to_string_with_suffix (level_suffix : string)
    (id : trait_clause_id) : string =
  trait_clause_id_to_pretty_string id ^ level_suffix

let trait_clause_id_to_string_for_env (env : fmt_env) (id : trait_clause_id) :
    string =
  trait_clause_id_to_string_with_suffix (current_binding_level_suffix env) id

let trait_clause_var_to_string (env : fmt_env) (var : trait_db_var) : string =
  trait_clause_id_to_string_with_suffix
    (de_bruijn_var_binding_level_suffix env var)
    (match var with
    | Bound (_, varid) | Free varid -> varid)

let region_db_var_to_string (env : fmt_env) (var : region_db_var) : string =
  match lookup_region_param env var with
  | None -> region_db_var_to_pretty_string var
  | Some r -> begin
      match r.name with
      | Some name -> name
      | None -> anonymous_region_param_to_string env var r
    end

let type_db_var_to_string (env : fmt_env) (var : type_db_var) : string =
  let find (generics : generic_params) varid =
    List.find_opt (fun (v : type_param) -> v.index = varid) generics.types
  in
  match lookup_var_in_env env find var with
  | None -> type_db_var_to_pretty_string var
  | Some r -> type_param_to_string r

let const_generic_db_var_to_string (env : fmt_env) (var : const_generic_db_var)
    : string =
  let find (generics : generic_params) varid =
    List.find_opt
      (fun (v : const_generic_param) -> v.index = varid)
      generics.const_generics
  in
  match lookup_var_in_env env find var with
  | None -> const_generic_db_var_to_pretty_string var
  | Some r -> r.name

let trait_db_var_to_string (env : fmt_env) (var : trait_db_var) : string =
  match de_bruijn_var_location env var with
  | None -> trait_db_var_to_pretty_string var
  | Some _ -> trait_clause_var_to_string env var

let region_to_string (env : fmt_env) (r : region) : string =
  match r with
  | RStatic -> "'static"
  | RErased -> "'_"
  | RBody id -> "'" ^ RegionId.to_string id
  | RVar var -> region_db_var_to_string env var

let pp_region_binder (pp_value : fmt_env -> Format.formatter -> 'c -> unit)
    (env : fmt_env) (fmt : Format.formatter) (rb : 'c region_binder) : unit =
  let env = fmt_env_push_regions env rb.binder_regions in
  match rb.binder_regions with
  | [] -> pp_value env fmt rb.binder_value
  | _ ->
      Format.fprintf fmt "for<%a> %a"
        (pp_sep_list ", " (fun fmt region ->
             pp_string fmt (region_param_to_string env region)))
        rb.binder_regions (pp_value env) rb.binder_value

let region_binder_to_string (value_to_string : fmt_env -> 'c -> string)
    (env : fmt_env) (rb : 'c region_binder) : string =
  pp_to_string (fun fmt ->
      pp_region_binder
        (fun env fmt value -> pp_string fmt (value_to_string env value))
        env fmt rb)

let rec pp_type_id (env : fmt_env) (fmt : Format.formatter) (id : type_id) :
    unit =
  match id with
  | TAdtId id -> pp_type_decl_id env fmt id
  | TTuple -> ()
  | TBuiltin aty -> (
      match aty with
      | TBox -> pp_string fmt "alloc::boxed::Box"
      | TStr -> pp_string fmt "str")

and pp_type_decl_id env fmt def_id =
  match find_short_name env (IdType def_id) with
  | Some name -> pp_name env fmt name
  | None -> pp_string fmt (type_decl_id_to_pretty_string def_id)

and pp_type_decl_ref (env : fmt_env) (fmt : Format.formatter)
    (tref : type_decl_ref) : unit =
  match tref.id with
  | TTuple ->
      let params, _trait_refs = generic_args_to_strings env tref.generics in
      let trailing_comma = if List.length params = 1 then "," else "" in
      Format.fprintf fmt "(%a%s)"
        (pp_sep_list ", " pp_string)
        params trailing_comma
  | id ->
      Format.fprintf fmt "%a%a" (pp_type_id env) id (pp_generic_args env)
        tref.generics

and pp_fun_decl_id (env : fmt_env) (fmt : Format.formatter) (id : FunDeclId.id)
    : unit =
  match find_short_name env (IdFun id) with
  | Some name -> pp_name env fmt name
  | None -> pp_string fmt (fun_decl_id_to_pretty_string id)

and pp_fun_decl_ref (env : fmt_env) (fmt : Format.formatter) (fn : fun_decl_ref)
    : unit =
  Format.fprintf fmt "%a%a" (pp_fun_decl_id env) fn.id
    (pp_generic_args_for_fn env)
    fn.generics

and pp_global_decl_id env fmt def_id =
  match find_short_name env (IdGlobal def_id) with
  | Some name -> pp_name env fmt name
  | None -> pp_string fmt (global_decl_id_to_pretty_string def_id)

and pp_global_decl_ref (env : fmt_env) (fmt : Format.formatter)
    (gr : global_decl_ref) : unit =
  Format.fprintf fmt "%a%a" (pp_global_decl_id env) gr.id (pp_generic_args env)
    gr.generics

and pp_trait_decl_id env fmt id =
  match find_short_name env (IdTraitDecl id) with
  | Some name -> pp_name env fmt name
  | None -> pp_string fmt (trait_decl_id_to_pretty_string id)

and pp_trait_impl_id env fmt id =
  match find_short_name env (IdTraitImpl id) with
  | Some name -> pp_name env fmt name
  | None -> pp_string fmt (trait_impl_id_to_pretty_string id)

and pp_trait_impl_ref (env : fmt_env) (fmt : Format.formatter)
    (iref : trait_impl_ref) : unit =
  Format.fprintf fmt "%a%a" (pp_trait_impl_id env) iref.id (pp_generic_args env)
    iref.generics

and pp_provenance (env : fmt_env) (fmt : Format.formatter) (pv : provenance) :
    unit =
  match pv with
  | ProvGlobal gref ->
      Format.fprintf fmt "prov_global(%a)" (pp_global_decl_ref env) gref
  | ProvFunction fn_ref ->
      Format.fprintf fmt "prov_fn(%a)" (pp_fun_decl_ref env) fn_ref
  | ProvUnknown -> pp_string fmt "prov_unknown"

and pp_byte (env : fmt_env) (fmt : Format.formatter) (cv : byte) : unit =
  match cv with
  | Uninit -> pp_string fmt "--"
  | Value b -> Format.fprintf fmt "%#4x" b
  | Provenance (p, i) -> Format.fprintf fmt "%a[%d]" (pp_provenance env) p i

and pp_unsizing_metadata (env : fmt_env) (fmt : Format.formatter)
    (meta : unsizing_metadata) : unit =
  match meta with
  | MetaLength len -> pp_constant_expr env fmt len
  | MetaVTable (_, vtable) -> pp_constant_expr env fmt vtable
  | MetaVTableUpcast fields ->
      Format.fprintf fmt " at [%a]"
        (pp_sep_list ", " (fun fmt id -> pp_string fmt (FieldId.to_string id)))
        fields
  | MetaUnknown -> pp_string fmt "?"

and pp_const_aggregate (env : fmt_env) (tref : type_decl_ref) opt_variant_id
    (fmt : Format.formatter) (fields : constant_expr list) : unit =
  match tref.id with
  | TTuple ->
      let trailing_comma = if List.length fields = 1 then "," else "" in
      Format.fprintf fmt "(%a%s)"
        (pp_sep_list ", " (pp_constant_expr env))
        fields trailing_comma
  | TAdtId def_id ->
      let fields =
        match adt_field_names env def_id opt_variant_id with
        | None ->
            fields
            |> List.mapi (fun i value ->
                   (FieldId.to_string (FieldId.of_int i), value))
        | Some field_names -> List.combine field_names fields
      in
      let pp_variant fmt =
        match opt_variant_id with
        | None -> pp_type_decl_id env fmt def_id
        | Some variant_id -> pp_adt_variant env def_id fmt variant_id
      in
      Format.fprintf fmt "%t { %a }" pp_variant
        (pp_sep_list ", " (fun fmt (field, value) ->
             Format.fprintf fmt "%s: %a" field (pp_constant_expr env) value))
        fields
  | TBuiltin _ -> raise (Failure "Unreachable")

and pp_constant_expr (env : fmt_env) (fmt : Format.formatter)
    (cv : constant_expr) : unit =
  match cv.kind with
  | CLiteral lit -> pp_literal fmt lit
  | CVar var -> pp_string fmt (const_generic_db_var_to_string env var)
  | CTraitConst (trait_ref, const_id) ->
      let name =
        GAstUtils.get_assoc_const_name env.crate
          trait_ref.trait_decl_ref.binder_value.id const_id
      in
      Format.fprintf fmt "%a::%s" (pp_trait_ref env) trait_ref name
  | CVTableRef trait_ref ->
      Format.fprintf fmt "&vtable_of(%a)" (pp_trait_ref env) trait_ref
  | CFnDef fn_ptr -> pp_fn_ptr env fmt fn_ptr
  | CFnPtr fn_ptr -> Format.fprintf fmt "fnptr(%a)" (pp_fn_ptr env) fn_ptr
  | CRawMemory bytes ->
      Format.fprintf fmt "RawMemory(%a)" (pp_sep_list ", " (pp_byte env)) bytes
  | COpaque reason -> Format.fprintf fmt "Opaque(%s)" reason
  | CAdt (variant_id, fields) -> begin
      match cv.ty with
      | TAdt tref -> pp_const_aggregate env tref variant_id fmt fields
      | _ -> pp_string fmt "malformed constant"
    end
  | CArray fields ->
      Format.fprintf fmt "[%a]" (pp_sep_list ", " (pp_constant_expr env)) fields
  | CGlobal gref -> pp_global_decl_ref env fmt gref
  | CPtrNoProvenance n -> Format.fprintf fmt "no-provenance %s" (Z.to_string n)
  | CRef (c, meta) ->
      Format.fprintf fmt "&%a" (pp_constant_expr env) c;
      Option.iter
        (fun meta ->
          Format.fprintf fmt " with_metadata(%a)" (pp_unsizing_metadata env)
            meta)
        meta
  | CPtr (ref_kind, c, meta) ->
      let ref_kind =
        match ref_kind with
        | RShared -> "&raw const"
        | RMut -> "&raw mut"
      in
      Format.fprintf fmt "%s %a" ref_kind (pp_constant_expr env) c;
      Option.iter
        (fun meta ->
          Format.fprintf fmt " with_metadata(%a)" (pp_unsizing_metadata env)
            meta)
        meta

and constant_expr_to_string env cv =
  pp_to_string (fun fmt -> pp_constant_expr env fmt cv)

and pp_builtin_fun_id (fmt : Format.formatter) (aid : builtin_fun_id) : unit =
  match aid with
  | BoxNew -> pp_string fmt "BoxNew"
  | ArrayToSliceShared -> pp_string fmt "ArrayToSliceShared"
  | ArrayToSliceMut -> pp_string fmt "ArrayToSliceMut"
  | ArrayRepeat -> pp_string fmt "ArrayRepeat"
  | Index { is_array; mutability; is_range } ->
      let ty = if is_array then "Array" else "Slice" in
      let op = if is_range then "SubSlice" else "Index" in
      Format.fprintf fmt "%s%s%a" ty op pp_ref_kind mutability
  | PtrFromParts mut -> Format.fprintf fmt "PtrFromParts%a" pp_ref_kind mut

and pp_fun_id (env : fmt_env) (fmt : Format.formatter) (fid : fun_id) : unit =
  match fid with
  | FRegular fid -> pp_fun_decl_id env fmt fid
  | FBuiltin aid -> Format.fprintf fmt "@%a" pp_builtin_fun_id aid

and pp_fn_ptr_kind (env : fmt_env) (fmt : Format.formatter) (r : fn_ptr_kind) :
    unit =
  match r with
  | TraitMethod (trait_ref, method_id, _) ->
      let method_name =
        GAstUtils.get_method_name env.crate
          trait_ref.trait_decl_ref.binder_value.id method_id
      in
      Format.fprintf fmt "%a::%s" (pp_trait_ref env) trait_ref method_name
  | FunId fid -> pp_fun_id env fmt fid

and pp_fn_ptr (env : fmt_env) (fmt : Format.formatter) (ptr : fn_ptr) : unit =
  Format.fprintf fmt "%a%a" (pp_fn_ptr_kind env) ptr.kind
    (pp_generic_args_for_fn env)
    ptr.generics

and pp_ty (env : fmt_env) (fmt : Format.formatter) (ty : ty) : unit =
  match ty with
  | TAdt tref -> pp_type_decl_ref env fmt tref
  | TVar tv -> pp_string fmt (type_db_var_to_string env tv)
  | TNever -> pp_string fmt "!"
  | TLiteral lit_ty -> pp_literal_type fmt lit_ty
  | TTraitType (trait_ref, type_id) ->
      let type_name =
        GAstUtils.get_assoc_type_name env.crate
          trait_ref.trait_decl_ref.binder_value.id type_id
      in
      Format.fprintf fmt "%a::%s" (pp_trait_ref env) trait_ref type_name
  | TRef (r, rty, ref_kind) -> (
      match ref_kind with
      | RMut ->
          Format.fprintf fmt "&%s mut %a" (region_to_string env r) (pp_ty env)
            rty
      | RShared ->
          Format.fprintf fmt "&%s %a" (region_to_string env r) (pp_ty env) rty)
  | TRawPtr (rty, ref_kind) -> (
      match ref_kind with
      | RMut -> Format.fprintf fmt "*mut %a" (pp_ty env) rty
      | RShared -> Format.fprintf fmt "*const %a" (pp_ty env) rty)
  | TFnPtr binder ->
      let env = fmt_env_push_regions env binder.binder_regions in
      let { inputs; output; is_unsafe } = binder.binder_value in
      let unsafe = if is_unsafe then "unsafe " else "" in
      Format.fprintf fmt "%sfn" unsafe;
      if binder.binder_regions <> [] then
        Format.fprintf fmt "<%a>"
          (pp_sep_list ", " (fun fmt region ->
               pp_string fmt (region_param_to_string env region)))
          binder.binder_regions;
      Format.fprintf fmt "(%a)" (pp_sep_list ", " (pp_ty env)) inputs;
      if not (ty_is_unit output) then
        Format.fprintf fmt " -> %a" (pp_ty env) output
  | TFnDef f ->
      let env = fmt_env_push_regions env f.binder_regions in
      if f.binder_regions <> [] then
        Format.fprintf fmt "for<%a> "
          (pp_sep_list ", " (fun fmt region ->
               pp_string fmt (region_param_to_string env region)))
          f.binder_regions;
      pp_fn_ptr env fmt f.binder_value
  | TDynTrait pred -> Format.fprintf fmt "(dyn %a)" (pp_dyn_predicate env) pred
  | TArray (ty, len) ->
      Format.fprintf fmt "[%a; %a]" (pp_ty env) ty (pp_constant_expr env) len
  | TSlice ty -> Format.fprintf fmt "[%a]" (pp_ty env) ty
  | TPtrMetadata ty -> Format.fprintf fmt "PtrMetadata<%a>" (pp_ty env) ty
  | TError msg -> Format.fprintf fmt "type_error(\"%s\")" msg

and ty_to_string env ty = pp_to_string (fun fmt -> pp_ty env fmt ty)

and dyn_trait_type_constraint_to_string (env : fmt_env)
    (ttc : trait_type_constraint) : (trait_clause_id * string) option =
  let rec target_clause_and_path path (tref : trait_ref) =
    match tref.kind with
    | ParentClause (parent, clause_id) ->
        target_clause_and_path
          (("parent_clause" ^ TraitClauseId.to_string clause_id) :: path)
          parent
    | Clause (Bound (_, clause_id)) | Clause (Free clause_id) ->
        Some (clause_id, List.rev path)
    | _ -> None
  in
  match target_clause_and_path [] ttc.trait_ref with
  | None -> None
  | Some (clause_id, path) ->
      let type_name =
        GAstUtils.get_assoc_type_name env.crate
          ttc.trait_ref.trait_decl_ref.binder_value.id ttc.type_id
      in
      let path =
        match path with
        | [] -> ""
        | _ -> String.concat "::" path ^ "::"
      in
      let ty = ty_to_string env ttc.ty in
      Some (clause_id, path ^ type_name ^ " = " ^ ty)

and pp_dyn_trait_clause (env : fmt_env)
    (constraints : (trait_clause_id * string list) list) (clause : trait_param)
    (fmt : Format.formatter) : unit =
  let clause_constraints =
    match List.assoc_opt clause.clause_id constraints with
    | None -> []
    | Some constraints -> constraints
  in
  let pp_trait env fmt (tr : trait_decl_ref) =
    let generics =
      match tr.generics.types with
      | _self_ty :: types -> { tr.generics with types }
      | [] -> tr.generics
    in
    let params, _trait_refs = generic_args_to_strings env generics in
    let params = params @ clause_constraints in
    pp_trait_decl_id env fmt tr.id;
    if params <> [] then
      Format.fprintf fmt "<%a>" (pp_sep_list ", " pp_string) params
  in
  pp_region_binder pp_trait env fmt clause.trait

and dyn_trait_clause_to_string env constraints clause =
  pp_to_string (fun fmt -> pp_dyn_trait_clause env constraints clause fmt)

and dyn_types_outlive_to_string (env : fmt_env)
    (rb : (ty, region) outlives_pred region_binder) : string option =
  match rb.binder_value with
  | _, RErased -> None
  | _, region ->
      Some
        (region_binder_to_string
           (fun env (_, region) -> region_to_string env region)
           env rb)

and pp_dyn_predicate (env : fmt_env) (fmt : Format.formatter)
    (pred : dyn_predicate) : unit =
  let params = pred.binder.binder_params in
  let env = fmt_env_push_generics_and_preds env params in
  let constraints =
    List.fold_left
      (fun constraints rb ->
        let env = fmt_env_push_regions env rb.binder_regions in
        match dyn_trait_type_constraint_to_string env rb.binder_value with
        | None -> constraints
        | Some (clause_id, constraint_) -> (
            match List.assoc_opt clause_id constraints with
            | None -> (clause_id, [ constraint_ ]) :: constraints
            | Some old ->
                (clause_id, old @ [ constraint_ ])
                :: List.remove_assoc clause_id constraints))
      [] params.trait_type_constraints
  in
  let trait_clauses =
    List.map (dyn_trait_clause_to_string env constraints) params.trait_clauses
  in
  let types_outlive =
    List.filter_map (dyn_types_outlive_to_string env) params.types_outlive
  in
  pp_sep_list " + " pp_string fmt (trait_clauses @ types_outlive)

(** Return two lists:
    - one for the regions, types, const generics
    - one for the trait refs *)
and generic_args_to_strings (env : fmt_env) (generics : generic_args) :
    string list * string list =
  let { regions; types; const_generics; trait_refs } = generics in
  let regions = List.map (region_to_string env) regions in
  let types = List.map (ty_to_string env) types in
  let cgs = List.map (constant_expr_to_string env) const_generics in
  let params = List.flatten [ regions; types; cgs ] in
  let trait_refs = List.map (trait_ref_to_string env) trait_refs in
  (params, trait_refs)

and pp_generic_args (env : fmt_env) (fmt : Format.formatter)
    (generics : generic_args) : unit =
  let params, trait_refs = generic_args_to_strings env generics in
  if params <> [] then
    Format.fprintf fmt "<%a>" (pp_sep_list ", " pp_string) params;
  if trait_refs <> [] then
    Format.fprintf fmt "[%a]" (pp_sep_list ", " pp_string) trait_refs

and pp_generic_args_for_fn (env : fmt_env) (fmt : Format.formatter)
    (generics : generic_args) : unit =
  pp_generic_args env fmt generics

and pp_trait_ref_kind (env : fmt_env)
    (implements : trait_decl_ref region_binder option) (fmt : Format.formatter)
    (kind : trait_ref_kind) : unit =
  match kind with
  | Self -> pp_string fmt "Self"
  | TraitImpl impl_ref -> pp_trait_impl_ref env fmt impl_ref
  | BuiltinOrAuto (_, _, types) ->
      let implements = Option.get implements in
      let types = AssocTypeId.Map.to_list types in
      Format.fprintf fmt "{built_in impl %a"
        (pp_region_binder pp_trait_decl_ref_as_impl env)
        implements;
      if types <> [] then
        Format.fprintf fmt " where %a"
          (pp_sep_list ", "
             (fun fmt (type_id, (assoc_ty : trait_assoc_ty_impl)) ->
               let name =
                 GAstUtils.get_assoc_type_name env.crate
                   implements.binder_value.id type_id
               in
               Format.fprintf fmt "%s  = %a" name (pp_ty env) assoc_ty.value))
          types;
      pp_string fmt "}"
  | Clause id -> pp_string fmt (trait_db_var_to_string env id)
  | ParentClause (tref, clause_id) ->
      Format.fprintf fmt "%a::parent_clause%s" (pp_trait_ref env) tref
        (TraitClauseId.to_string clause_id)
  | ItemClause (tref, type_id, clause_id) ->
      let type_name =
        GAstUtils.get_assoc_type_name env.crate
          tref.trait_decl_ref.binder_value.id type_id
      in
      Format.fprintf fmt "(%a::%s::[%s])" (pp_trait_ref env) tref type_name
        (trait_clause_id_to_pretty_string clause_id)
  | Dyn -> pp_region_binder pp_trait_decl_ref env fmt (Option.get implements)
  | UnknownTrait msg -> Format.fprintf fmt "UNKNOWN(%s)" msg

and pp_trait_ref (env : fmt_env) (fmt : Format.formatter) (tr : trait_ref) :
    unit =
  pp_trait_ref_kind env (Some tr.trait_decl_ref) fmt tr.kind

and trait_ref_to_string env tr =
  pp_to_string (fun fmt -> pp_trait_ref env fmt tr)

and pp_trait_decl_ref (env : fmt_env) (fmt : Format.formatter)
    (tr : trait_decl_ref) : unit =
  Format.fprintf fmt "%a%a" (pp_trait_decl_id env) tr.id (pp_generic_args env)
    tr.generics

and pp_trait_decl_ref_as_impl (env : fmt_env) (fmt : Format.formatter)
    (tr : trait_decl_ref) : unit =
  match tr.generics.types with
  | self_ty :: types ->
      let generics = { tr.generics with types } in
      Format.fprintf fmt "%a for %a" (pp_trait_decl_ref env)
        { tr with generics } (pp_ty env) self_ty
  | [] -> pp_trait_decl_ref env fmt tr

and pp_impl_elem (env : fmt_env) (fmt : Format.formatter) (elem : impl_elem) :
    unit =
  match elem with
  | ImplElemTy bound_ty ->
      (* Locally replace the generics and the predicates *)
      let env = fmt_env_push_generics_and_preds env bound_ty.binder_params in
      pp_ty env fmt bound_ty.binder_value
  | ImplElemTrait impl_id -> begin
      match TraitImplId.Map.find_opt impl_id env.crate.trait_impls with
      | None -> Format.fprintf fmt "impl#%s" (TraitImplId.to_string impl_id)
      | Some impl ->
          (* Locally replace the generics and the predicates *)
          let env = fmt_env_push_generics_and_preds env impl.generics in
          Format.fprintf fmt "impl %a"
            (pp_trait_decl_ref_as_impl env)
            impl.impl_trait
    end

and pp_path_elem (env : fmt_env) (fmt : Format.formatter) (e : path_elem) : unit
    =
  match e with
  | PeIdent (s, d) ->
      pp_string fmt s;
      if d <> Disambiguator.zero then
        Format.fprintf fmt "#%s" (Disambiguator.to_string d)
  | PeImpl impl -> Format.fprintf fmt "{%a}" (pp_impl_elem env) impl
  | PeInstantiated binder ->
      let anon_params =
        {
          binder.binder_params with
          regions =
            List.map
              (fun (r : region_param) -> { r with name = Some "_" })
              binder.binder_params.regions;
          types =
            List.map
              (fun (t : type_param) -> { t with name = "_" })
              binder.binder_params.types;
          const_generics =
            List.map
              (fun (c : const_generic_param) -> { c with name = "_" })
              binder.binder_params.const_generics;
          regions_outlive = [];
          types_outlive = [];
          trait_type_constraints = [];
        }
      in
      let env = fmt_env_push_generics_and_preds env anon_params in
      let explicits, _ = generic_args_to_strings env binder.binder_value in
      Format.fprintf fmt "<%a>" (pp_sep_list ", " pp_string) explicits
  | PeTarget target -> pp_string fmt target

and pp_name (env : fmt_env) (fmt : Format.formatter) (n : name) : unit =
  let env = { env with generics = [] } in
  pp_sep_list "::" (pp_path_elem env) fmt n

and name_to_string env n = pp_to_string (fun fmt -> pp_name env fmt n)

and pp_raw_attribute (fmt : Format.formatter) (attr : raw_attribute) : unit =
  pp_string fmt attr.path;
  Option.iter (fun args -> Format.fprintf fmt "(%s)" args) attr.args

and pp_trait_param (env : fmt_env) (fmt : Format.formatter)
    (clause : trait_param) : unit =
  let clause_id = trait_clause_id_to_string_for_env env clause.clause_id in
  Format.fprintf fmt "[%s]: %a" clause_id
    (pp_region_binder pp_trait_decl_ref env)
    clause.trait

and trait_param_to_string env clause =
  pp_to_string (fun fmt -> pp_trait_param env fmt clause)

and generic_params_to_strings (env : fmt_env) (generics : generic_params) :
    string list * string list =
  let ({ regions; types; const_generics; trait_clauses; _ } : generic_params) =
    generics
  in
  let regions = List.map (region_param_to_string env) regions in
  let types = List.map type_param_to_string types in
  let cgs =
    List.map (const_generic_param_to_string (ty_to_string env)) const_generics
  in
  let params = List.flatten [ regions; types; cgs ] in
  let trait_clauses = List.map (trait_param_to_string env) trait_clauses in
  (params, trait_clauses)

and pp_adt_variant (env : fmt_env) (def_id : TypeDeclId.id)
    (fmt : Format.formatter) (variant_id : VariantId.id) : unit =
  match TypeDeclId.Map.find_opt def_id env.crate.type_decls with
  | None ->
      Format.fprintf fmt "%s::%s"
        (type_decl_id_to_pretty_string def_id)
        (variant_id_to_pretty_string variant_id)
  | Some def -> begin
      match def.kind with
      | Enum variants ->
          let variant = VariantId.nth variants variant_id in
          Format.fprintf fmt "%a::%s" (pp_type_decl_id env) def_id
            variant.variant_name
      | _ -> raise (Failure "Unreachable")
    end

and adt_field_names (env : fmt_env) (def_id : TypeDeclId.id)
    (opt_variant_id : VariantId.id option) : string list option =
  match TypeDeclId.Map.find_opt def_id env.crate.type_decls with
  | None -> None
  | Some { kind = Opaque; _ } -> None
  | Some def ->
      let fields = type_decl_get_fields def opt_variant_id in
      (* There are two cases: either all the fields have names, or none
         of them has names *)
      let has_names =
        List.exists (fun f -> Option.is_some f.field_name) fields
      in
      if has_names then
        let fields = List.map (fun f -> Option.get f.field_name) fields in
        Some fields
      else None

let pp_field (env : fmt_env) (fmt : Format.formatter) (f : field) : unit =
  match f.field_name with
  | Some field_name ->
      Format.fprintf fmt "%s: %s" field_name (ty_to_string env f.field_ty)
  | None -> pp_string fmt (ty_to_string env f.field_ty)

let pp_variant (env : fmt_env) (fmt : Format.formatter) (v : variant) : unit =
  if v.fields = [] then pp_string fmt v.variant_name
  else
    Format.fprintf fmt "%s(%a)" v.variant_name
      (pp_sep_list ", " (pp_field env))
      v.fields

let pp_trait_type_constraint (env : fmt_env) (fmt : Format.formatter)
    (ttc : trait_type_constraint) : unit =
  let { trait_ref; type_id; ty } = ttc in
  let type_name =
    GAstUtils.get_assoc_type_name env.crate
      trait_ref.trait_decl_ref.binder_value.id type_id
  in
  Format.fprintf fmt "%s::%s = %s"
    (trait_ref_to_string env trait_ref)
    type_name (ty_to_string env ty)

let trait_type_constraint_to_string env ttc =
  pp_to_string (fun fmt -> pp_trait_type_constraint env fmt ttc)

(** Helper to format "where" clauses *)
let pp_clauses (indent : string) (indent_incr : string) (fmt : Format.formatter)
    (clauses : string list) : unit =
  match clauses with
  | [] -> ()
  | clauses ->
      Format.fprintf fmt "\n%swhere\n" indent;
      pp_sep_list "\n"
        (fun fmt clause ->
          Format.fprintf fmt "%s%s," (indent ^ indent_incr) clause)
        fmt clauses

let clauses_to_string indent indent_incr clauses =
  pp_to_string (fun fmt -> pp_clauses indent indent_incr fmt clauses)

(** Helper to format "where" clauses *)
let predicates_and_trait_clauses_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) (generics : generic_params) : string list * string =
  let params, trait_clauses = generic_params_to_strings env generics in
  let regions_outlive =
    let outlive_to_string env (x, y) =
      region_to_string env x ^ " : " ^ region_to_string env y
    in
    List.map
      (region_binder_to_string outlive_to_string env)
      generics.regions_outlive
  in
  let types_outlive =
    let outlive_to_string env (x, y) =
      ty_to_string env x ^ " : " ^ region_to_string env y
    in
    List.map
      (region_binder_to_string outlive_to_string env)
      generics.types_outlive
  in
  let trait_type_constraints =
    List.map
      (region_binder_to_string trait_type_constraint_to_string env)
      generics.trait_type_constraints
  in
  (* Split between the inherited clauses and the local clauses *)
  let clauses =
    clauses_to_string indent indent_incr
      (List.concat
         [
           trait_clauses; types_outlive; regions_outlive; trait_type_constraints;
         ])
  in
  (params, clauses)

let pp_generic_params_single_line (env : fmt_env) (fmt : Format.formatter)
    (generics : generic_params) : unit =
  let params, trait_clauses = generic_params_to_strings env generics in
  let regions_outlive =
    List.map
      (region_binder_to_string
         (fun env (x, y) ->
           region_to_string env x ^ " : " ^ region_to_string env y)
         env)
      generics.regions_outlive
  in
  let types_outlive =
    List.map
      (region_binder_to_string
         (fun env (x, y) -> ty_to_string env x ^ " : " ^ region_to_string env y)
         env)
      generics.types_outlive
  in
  let trait_type_constraints =
    List.map
      (region_binder_to_string trait_type_constraint_to_string env)
      generics.trait_type_constraints
  in
  let all =
    List.concat
      [
        params;
        trait_clauses;
        types_outlive;
        regions_outlive;
        trait_type_constraints;
      ]
  in
  if all <> [] then Format.fprintf fmt "<%a>" (pp_sep_list ", " pp_string) all

let generic_params_to_string_single_line env generics =
  pp_to_string (fun fmt -> pp_generic_params_single_line env fmt generics)

let pp_item_intro (env : fmt_env) (indent : string) (keyword : string)
    (id : item_id) (fmt : Format.formatter) (meta : item_meta) : unit =
  let full_name = name_to_string env meta.name in
  let name, full_name_comment =
    match has_short_name env id with
    | Some short_name ->
        (name_to_string env short_name, "// Full name: " ^ full_name ^ "\n")
    | None -> (full_name, "")
  in
  let lang_item =
    match meta.lang_item with
    | None -> ""
    | Some id -> indent ^ "#[lang_item(\"" ^ id ^ "\")]\n"
  in
  let public = if meta.attr_info.public then "pub " else "" in
  Format.fprintf fmt "%s%s%s%s%s %s" full_name_comment lang_item indent public
    keyword name

let item_intro_to_string env indent keyword id meta =
  pp_to_string (fun fmt -> pp_item_intro env indent keyword id fmt meta)

let pp_type_decl (env : fmt_env) (fmt : Format.formatter) (def : type_decl) :
    unit =
  let keyword =
    match def.kind with
    | Struct _ -> "struct"
    | Union _ -> "union"
    | Enum _ -> "enum"
    | Alias _ -> "type"
    | Opaque | TDeclError _ -> "opaque type"
  in
  let intro =
    item_intro_to_string env "" keyword (IdType def.def_id) def.item_meta
  in
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env "" tab_incr def.generics
  in
  let params =
    if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
  in
  let nl_or_space = if clauses = "" then " " else "\n" in
  match def.kind with
  | Struct fields ->
      Format.fprintf fmt "%s%s%s%s{" intro params clauses nl_or_space;
      if fields <> [] then (
        pp_string fmt "\n";
        List.iter
          (fun field -> Format.fprintf fmt "  %a,\n" (pp_field env) field)
          fields);
      pp_string fmt "}"
  | Enum variants ->
      Format.fprintf fmt "%s%s%s%s{\n" intro params clauses nl_or_space;
      List.iter
        (fun variant -> Format.fprintf fmt "  %a,\n" (pp_variant env) variant)
        variants;
      pp_string fmt "}"
  | Union fields ->
      Format.fprintf fmt "%s%s%s%s{\n" intro params clauses nl_or_space;
      List.iter
        (fun field -> Format.fprintf fmt "  %a,\n" (pp_field env) field)
        fields;
      pp_string fmt "}"
  | Alias ty ->
      Format.fprintf fmt "%s%s%s = %s" intro params clauses
        (ty_to_string env ty)
  | Opaque -> Format.fprintf fmt "%s%s%s" intro params clauses
  | TDeclError err ->
      Format.fprintf fmt "%s%s%s = ERROR(%s)" intro params clauses err

let adt_field_to_string (env : fmt_env) (def_id : TypeDeclId.id)
    (opt_variant_id : VariantId.id option) (field_id : FieldId.id) :
    string option =
  match TypeDeclId.Map.find_opt def_id env.crate.type_decls with
  | None -> None
  | Some { kind = Opaque; _ } -> None
  | Some def ->
      let fields = type_decl_get_fields def opt_variant_id in
      let field = FieldId.nth fields field_id in
      field.field_name

let local_id_to_pretty_string (id : local_id) : string =
  "_" ^ LocalId.to_string id

let local_to_string (v : local) : string =
  match v.name with
  | None -> "_" ^ LocalId.to_string v.index
  | Some name -> name ^ "_" ^ LocalId.to_string v.index

let local_id_to_string (env : fmt_env) (id : LocalId.id) : string =
  match List.find_opt (fun (i, _) -> i = id) env.locals with
  | None -> local_id_to_pretty_string id
  | Some (_, name) -> (
      match name with
      | None -> local_id_to_pretty_string id
      | Some name -> name ^ "_" ^ LocalId.to_string id)

let rec pp_projection_elem (env : fmt_env) (sub : string)
    (fmt : Format.formatter) (pe : projection_elem) : unit =
  match pe with
  | Deref -> Format.fprintf fmt "(*%s)" sub
  | ProjIndex (off, from_end) ->
      let idx_pre = if from_end then "-" else "" in
      Format.fprintf fmt "%s[%s%s]" sub idx_pre (operand_to_string env off)
  | Subslice (from, to_, from_end) ->
      let to_ =
        if from_end then "-" ^ operand_to_string env to_
        else operand_to_string env to_
      in
      Format.fprintf fmt "%s[%s..%s]" sub (operand_to_string env from) to_
  | Field (ProjTuple _, fid) ->
      Format.fprintf fmt "%s.%s" sub (FieldId.to_string fid)
  | Field (ProjAdt (adt_id, opt_variant_id), fid) -> (
      let field_name =
        match adt_field_to_string env adt_id opt_variant_id fid with
        | Some field_name -> field_name
        | None -> FieldId.to_string fid
      in
      match opt_variant_id with
      | None -> Format.fprintf fmt "(%s).%s" sub field_name
      | Some variant_id ->
          Format.fprintf fmt "(%s as variant %a).%s" sub
            (pp_adt_variant env adt_id)
            variant_id field_name)
  | PtrMetadata -> Format.fprintf fmt "%s.metadata" sub

and pp_place (env : fmt_env) (fmt : Format.formatter) (p : place) : unit =
  match p.kind with
  | PlaceLocal var_id -> pp_string fmt (local_id_to_string env var_id)
  | PlaceProjection (subplace, pe) ->
      let subplace = place_to_string env subplace in
      pp_projection_elem env subplace fmt pe
  | PlaceGlobal global_ref ->
      Format.fprintf fmt "%a%a" (pp_global_decl_id env) global_ref.id
        (pp_generic_args env) global_ref.generics

and place_to_string env p = pp_to_string (fun fmt -> pp_place env fmt p)

and pp_cast_kind (env : fmt_env) (fmt : Format.formatter) (cast : cast_kind) :
    unit =
  match cast with
  | CastScalar (src, tgt) ->
      Format.fprintf fmt "cast<%a, %a>" pp_literal_type src pp_literal_type tgt
  | CastFnPtr (src, tgt) | CastRawPtr (src, tgt) ->
      Format.fprintf fmt "cast<%a, %a>" (pp_ty env) src (pp_ty env) tgt
  | CastTransmute (src, tgt) ->
      Format.fprintf fmt "transmute<%a, %a>" (pp_ty env) src (pp_ty env) tgt
  | CastUnsize (src, tgt, meta) ->
      Format.fprintf fmt "unsize_cast<%a, %a, %a>" (pp_ty env) src (pp_ty env)
        tgt (pp_unsizing_metadata env) meta
  | CastConcretize (src, tgt) ->
      Format.fprintf fmt "concretize<%a, %a>" (pp_ty env) src (pp_ty env) tgt

and pp_nullop (env : fmt_env) (fmt : Format.formatter) (op : nullop) : unit =
  match op with
  | SizeOf -> pp_string fmt "size_of"
  | AlignOf -> pp_string fmt "align_of"
  | OffsetOf (ty, opt_variant_id, field_id) ->
      let def_id =
        match ty.id with
        | TAdtId def_id -> Some def_id
        | _ -> None
      in
      let variant_name =
        match (def_id, opt_variant_id) with
        | Some def_id, Some variant_id -> (
            match TypeDeclId.Map.find_opt def_id env.crate.type_decls with
            | Some { kind = Enum variants; _ } ->
                (VariantId.nth variants variant_id).variant_name ^ "."
            | _ -> VariantId.to_string variant_id ^ ".")
        | _ -> ""
      in
      let field_name =
        match def_id with
        | Some def_id -> (
            match adt_field_to_string env def_id opt_variant_id field_id with
            | Some name -> name
            | None -> FieldId.to_string field_id)
        | None -> FieldId.to_string field_id
      in
      Format.fprintf fmt "offset_of(%a.%s%s)" (pp_type_decl_ref env) ty
        variant_name field_name
  | UbChecks -> pp_string fmt "ub_checks"
  | ContractChecks -> pp_string fmt "contract_checks"
  | OverflowChecks -> pp_string fmt "overflow_checks"

and pp_unop (env : fmt_env) (fmt : Format.formatter) (unop : unop) : unit =
  match unop with
  | Not -> pp_string fmt "~"
  | Neg om -> Format.fprintf fmt "%a.-" pp_overflow_mode om
  | Cast cast_kind -> pp_cast_kind env fmt cast_kind

and pp_overflow_mode (fmt : Format.formatter) (mode : overflow_mode) : unit =
  match mode with
  | OWrap -> pp_string fmt "wrap"
  | OUB -> pp_string fmt "ub"
  | OPanic -> pp_string fmt "panic"

and pp_binop (fmt : Format.formatter) (binop : binop) : unit =
  match binop with
  | BitXor -> pp_string fmt "^"
  | BitAnd -> pp_string fmt "&"
  | BitOr -> pp_string fmt "|"
  | Eq -> pp_string fmt "=="
  | Lt -> pp_string fmt "<"
  | Le -> pp_string fmt "<="
  | Ne -> pp_string fmt "!="
  | Ge -> pp_string fmt ">="
  | Gt -> pp_string fmt ">"
  | Div om -> Format.fprintf fmt "%a./" pp_overflow_mode om
  | Rem om -> Format.fprintf fmt "%a.%%" pp_overflow_mode om
  | Add om -> Format.fprintf fmt "%a.+" pp_overflow_mode om
  | Sub om -> Format.fprintf fmt "%a.-" pp_overflow_mode om
  | Mul om -> Format.fprintf fmt "%a.*" pp_overflow_mode om
  | Shl om -> Format.fprintf fmt "%a.<<" pp_overflow_mode om
  | Shr om -> Format.fprintf fmt "%a.>>" pp_overflow_mode om
  | AddChecked -> pp_string fmt "checked.+"
  | SubChecked -> pp_string fmt "checked.-"
  | MulChecked -> pp_string fmt "checked.*"
  | Cmp -> pp_string fmt "cmp"
  | Offset -> pp_string fmt "offset"

and pp_operand (env : fmt_env) (fmt : Format.formatter) (op : operand) : unit =
  match op with
  | Copy p -> Format.fprintf fmt "copy %s" (place_to_string env p)
  | Move p -> Format.fprintf fmt "move %s" (place_to_string env p)
  | Constant cv ->
      Format.fprintf fmt "const %s" (constant_expr_to_string env cv)

and operand_to_string env op = pp_to_string (fun fmt -> pp_operand env fmt op)

and operand_ty (op : operand) : ty =
  match op with
  | Copy p | Move p -> p.ty
  | Constant cv -> cv.ty

and pp_aggregate (env : fmt_env) (agg : aggregate_kind) (fmt : Format.formatter)
    (fields : operand list) : unit =
  let fields = List.map (operand_to_string env) fields in
  match agg with
  | AggregatedAdt (tref, opt_variant_id, opt_field_id) -> (
      match tref.id with
      | TTuple ->
          let trailing_comma = if List.length fields = 1 then "," else "" in
          Format.fprintf fmt "(%a%s)"
            (pp_sep_list ", " pp_string)
            fields trailing_comma
      | TBuiltin TBox ->
          Format.fprintf fmt "Box(%a)" (pp_sep_list ", " pp_string) fields
      | TBuiltin TStr ->
          Format.fprintf fmt "[%a]" (pp_sep_list ", " pp_string) fields
      | TAdtId def_id ->
          let pp_variant fmt =
            match opt_variant_id with
            | None -> pp_type_decl_id env fmt def_id
            | Some variant_id -> pp_adt_variant env def_id fmt variant_id
          in
          let fields =
            match adt_field_names env def_id opt_variant_id with
            | None ->
                fields
                |> List.mapi (fun i value ->
                       FieldId.to_string (FieldId.of_int i) ^ ": " ^ value)
            | Some field_names ->
                let field_names =
                  match opt_field_id with
                  | None -> field_names
                  (* Only keep the selected field *)
                  | Some field_id ->
                      [ List.nth field_names (FieldId.to_int field_id) ]
                in
                let fields = List.combine field_names fields in
                List.map (fun (field, value) -> field ^ ": " ^ value) fields
          in
          Format.fprintf fmt "%t { %a }" pp_variant
            (pp_sep_list ", " pp_string)
            fields)
  | AggregatedArray (_ty, _cg) ->
      Format.fprintf fmt "[%a]" (pp_sep_list ", " pp_string) fields
  | AggregatedRawPtr (_, refk) ->
      let refk =
        match refk with
        | RShared -> "const"
        | RMut -> "mut "
      in
      Format.fprintf fmt "*%s (%a)" refk (pp_sep_list ", " pp_string) fields

and pp_rvalue (env : fmt_env) (fmt : Format.formatter) (rv : rvalue) : unit =
  match rv with
  | Use op -> pp_operand env fmt op
  | RvRef (p, bk, op) -> begin
      let p = place_to_string env p in
      let borrow_kind =
        match bk with
        | BShared -> "&"
        | BMut -> "&mut "
        | BTwoPhaseMut -> "&two-phase-mut "
        | BUniqueImmutable -> "&uniq "
        | BShallow -> "&shallow "
      in
      if ty_is_unit (operand_ty op) then Format.fprintf fmt "%s%s" borrow_kind p
      else
        Format.fprintf fmt "%s%s with_metadata(%s)" borrow_kind p
          (operand_to_string env op)
    end
  | RawPtr (p, pk, op) -> begin
      let p = place_to_string env p in
      let ptr_kind =
        match pk with
        | RShared -> "&raw const "
        | RMut -> "&raw mut "
      in
      if ty_is_unit (operand_ty op) then Format.fprintf fmt "%s%s" ptr_kind p
      else
        Format.fprintf fmt "%s%s with_metadata(%s)" ptr_kind p
          (operand_to_string env op)
    end
  | NullaryOp (op, ty) ->
      Format.fprintf fmt "%a<%a>" (pp_nullop env) op (pp_ty env) ty
  | UnaryOp (unop, op) ->
      Format.fprintf fmt "%a(%a)" (pp_unop env) unop (pp_operand env) op
  | BinaryOp (binop, op1, op2) ->
      Format.fprintf fmt "%a %a %a" (pp_operand env) op1 pp_binop binop
        (pp_operand env) op2
  | Discriminant p ->
      Format.fprintf fmt "@discriminant(%s)" (place_to_string env p)
  | Len (place, _, _) ->
      Format.fprintf fmt "len(%s)" (place_to_string env place)
  | Repeat (v, _, len) ->
      Format.fprintf fmt "[%s; %s]" (operand_to_string env v)
        (constant_expr_to_string env len)
  | Aggregate (akind, ops) -> pp_aggregate env akind fmt ops

let pp_fn_operand (env : fmt_env) (fmt : Format.formatter) (op : fn_operand) :
    unit =
  match op with
  | FnOpRegular func -> pp_fn_ptr env fmt func
  | FnOpDynamic op -> Format.fprintf fmt "(%a)" (pp_operand env) op

let pp_call (env : fmt_env) (indent : string) (fmt : Format.formatter)
    (call : call) : unit =
  Format.fprintf fmt "%s%a = %a(%a)" indent (pp_place env) call.dest
    (pp_fn_operand env) call.func
    (pp_sep_list ", " (pp_operand env))
    call.args

let pp_assertion (env : fmt_env) (fmt : Format.formatter) (a : assertion) : unit
    =
  let check_kind =
    match a.check_kind with
    | None -> ""
    | Some (BoundsCheck _) -> " (bounds_check)"
    | Some (Overflow _) -> " (overflow)"
    | Some (OverflowNeg _) -> " (overflow_neg)"
    | Some (DivisionByZero _) -> " (division_by_zero)"
    | Some (RemainderByZero _) -> " (remainder_by_zero)"
    | Some (MisalignedPointerDereference _) ->
        " (misaligned_pointer_dereference)"
    | Some NullPointerDereference -> " (null_pointer_dereference)"
    | Some (InvalidEnumConstruction _) -> " (invalid_enum_construction)"
  in
  Format.fprintf fmt "assert(%s == %s)%s"
    (operand_to_string env a.cond)
    (Bool.to_string a.expected)
    check_kind

let pp_abort_kind (env : fmt_env) (fmt : Format.formatter) (a : abort_kind) :
    unit =
  match a with
  | Panic None -> pp_string fmt "panic"
  | Panic (Some name) ->
      Format.fprintf fmt "panic(%s)" (name_to_string env name)
  | UndefinedBehavior -> pp_string fmt "undefined_behavior"
  | UnwindTerminate -> pp_string fmt "unwind_terminate"

(** Small helper *)
let pp_fun_sig_with_name (env : fmt_env) (indent : string)
    (indent_incr : string) (attribute : string option) (name : string option)
    (args : local list option) (fmt : Format.formatter) (sg : bound_fun_sig) :
    unit =
  let { item_binder_params = generics; item_binder_value = sg; _ } = sg in
  let env = fmt_env_replace_generics_and_preds env generics in
  let ty_to_string = ty_to_string env in

  (* Unsafe keyword *)
  let unsafe = if sg.is_unsafe then "unsafe " else "" in

  (* Generics and predicates *)
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr generics
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in

  (* Return type *)
  let ret_ty = sg.output in
  let ret_ty = if ty_is_unit ret_ty then "" else " -> " ^ ty_to_string ret_ty in

  (* Arguments *)
  let pp_args fmt =
    match args with
    | None ->
        pp_sep_list ", "
          (fun fmt ty -> pp_string fmt (ty_to_string ty))
          fmt sg.inputs
    | Some args ->
        let args = List.combine args sg.inputs in
        pp_sep_list ", "
          (fun fmt (var, rty) ->
            Format.fprintf fmt "%s : %s" (local_to_string var)
              (ty_to_string rty))
          fmt args
  in

  let attribute =
    match attribute with
    | None -> ""
    | Some attr -> attr ^ " "
  in
  let name =
    match name with
    | None -> ""
    | Some name -> " " ^ name
  in
  Format.fprintf fmt "%s%s%sfn%s%s(%t)%s%s" indent attribute unsafe name params
    pp_args ret_ty clauses

let pp_fun_sig (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (sg : fun_sig item_binder) : unit =
  let { item_binder_params = generics; item_binder_value = sg; _ } = sg in
  let env = fmt_env_replace_generics_and_preds env generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr generics
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in
  Format.fprintf fmt "%s%sfn%s(" indent
    (if sg.is_unsafe then "unsafe " else "")
    params;
  pp_sep_list ", "
    (fun fmt ty -> pp_string fmt (ty_to_string env ty))
    fmt sg.inputs;
  pp_string fmt ")";
  if not (ty_is_unit sg.output) then
    Format.fprintf fmt " -> %s" (ty_to_string env sg.output);
  pp_string fmt clauses

let pp_locals (env : fmt_env) (indent : string) (fmt : Format.formatter)
    (locals : locals) : unit =
  let pp_local_decl fmt var =
    let kind =
      if var.index = LocalId.zero then "return"
      else if LocalId.to_int var.index <= locals.arg_count then
        "arg #" ^ LocalId.to_string var.index
      else
        match var.name with
        | Some _ -> "local"
        | None -> "anonymous local"
    in
    Format.fprintf fmt "%slet %s: %s; // %s" indent (local_to_string var)
      (ty_to_string env var.local_ty)
      kind
  in
  pp_sep_list "\n" pp_local_decl fmt locals.locals

let pp_trait_decl (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (def : trait_decl) : unit =
  let intro =
    item_intro_to_string env indent "trait" (IdTraitDecl def.def_id)
      def.item_meta
  in
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr def.generics
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in
  let indent1 = indent ^ indent_incr in
  let consts : trait_assoc_const list = AssocConstId.Map.values def.consts in
  let types = AssocTypeId.Map.values def.types in
  let methods = TraitMethodId.Map.values def.methods in
  Format.fprintf fmt "%s%s%s" intro params clauses;
  if def.implied_clauses <> [] || consts <> [] || types <> [] || methods <> []
  then (
    pp_string fmt "\n{\n";
    List.iter
      (fun clause ->
        Format.fprintf fmt "%sparent_clause%s : %s\n" indent1
          (TraitClauseId.to_string clause.clause_id)
          (trait_param_to_string env clause))
      def.implied_clauses;
    List.iter
      (fun (c : trait_assoc_const) ->
        Format.fprintf fmt "%sconst %s : %s\n" indent1 c.name
          (ty_to_string env c.ty))
      consts;
    List.iter
      (fun (bound_ty : trait_assoc_ty binder) ->
        let env = fmt_env_push_generics_and_preds env bound_ty.binder_params in
        let params =
          generic_params_to_string_single_line env bound_ty.binder_params
        in
        Format.fprintf fmt "%stype %s%s" indent1 bound_ty.binder_value.name
          params;
        if bound_ty.binder_value.implied_clauses <> [] then (
          Format.fprintf fmt "\n%swhere\n" indent1;
          List.iter
            (fun c ->
              Format.fprintf fmt "%simplied_clause_%s : %s\n"
                (indent1 ^ indent_incr)
                (TraitClauseId.to_string c.clause_id)
                (trait_param_to_string env c))
            bound_ty.binder_value.implied_clauses);
        pp_string fmt "\n")
      types;
    List.iter
      (fun (m : trait_method binder) ->
        let env = fmt_env_push_generics_and_preds env m.binder_params in
        let params = generic_params_to_string_single_line env m.binder_params in
        Format.fprintf fmt "%sfn %s%s = %a\n" indent1 m.binder_value.name params
          (pp_fun_decl_ref env) m.binder_value.item)
      methods;
    (match def.vtable with
    | Some vtb_ref ->
        Format.fprintf fmt "%svtable: %a\n" indent1 (pp_type_decl_ref env)
          vtb_ref
    | None -> Format.fprintf fmt "%snon-dyn-compatible\n" indent1);
    pp_string fmt "}")

let pp_trait_impl (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (def : trait_impl) : unit =
  Format.fprintf fmt "%s// Full name: %s\n" indent
    (name_to_string env def.item_meta.name);
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr def.generics
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in
  let indent1 = indent ^ indent_incr in
  let trait_id = def.impl_trait.id in
  Format.fprintf fmt "%simpl%s %a%s" indent params
    (pp_trait_decl_ref_as_impl env)
    def.impl_trait clauses;
  pp_string fmt (if clauses = "" then " {" else "\n{");
  pp_string fmt "\n";
  List.iteri
    (fun i trait_ref ->
      Format.fprintf fmt "%sparent_clause%s = %s\n" indent1 (string_of_int i)
        (trait_ref_to_string env trait_ref))
    def.implied_trait_refs;
  AssocConstId.Map.to_list def.consts
  |> List.iter (fun (const_id, gref) ->
         let name =
           GAstUtils.get_assoc_const_name env.crate trait_id const_id
         in
         Format.fprintf fmt "%sconst %s = %a\n" indent1 name
           (pp_global_decl_ref env) gref);
  AssocTypeId.Map.to_list def.types
  |> List.iter (fun (type_id, bound_ty) ->
         let name = GAstUtils.get_assoc_type_name env.crate trait_id type_id in
         let env = fmt_env_push_generics_and_preds env bound_ty.binder_params in
         let params =
           generic_params_to_string_single_line env bound_ty.binder_params
         in
         Format.fprintf fmt "%stype %s%s = %s\n" indent1 name params
           (ty_to_string env bound_ty.binder_value.value));
  TraitMethodId.Map.to_list def.methods
  |> List.iter (fun (method_id, (f : fun_decl_ref binder)) ->
         let name = GAstUtils.get_method_name env.crate trait_id method_id in
         let env = fmt_env_push_generics_and_preds env f.binder_params in
         let params =
           generic_params_to_string_single_line env f.binder_params
         in
         Format.fprintf fmt "%sfn %s%s = %a\n" indent1 name params
           (pp_fun_decl_ref env) f.binder_value);
  (match def.vtable with
  | Some vtb_ref ->
      Format.fprintf fmt "%svtable: %a\n" indent1 (pp_global_decl_ref env)
        vtb_ref
  | None -> Format.fprintf fmt "%snon-dyn-compatible\n" indent1);
  pp_string fmt "}"

let pp_global_decl (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (def : global_decl) : unit =
  let keyword =
    match def.global_kind with
    | Static -> "static"
    | NamedConst | AnonConst -> "const"
  in
  let intro =
    item_intro_to_string env indent keyword (IdGlobal def.def_id) def.item_meta
  in
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr def.generics
  in
  let params =
    if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
  in
  Format.fprintf fmt "%s%s: %a%s%s= %a()" intro params (pp_ty env) def.ty
    clauses
    (if clauses = "" then " " else "\n ")
    (pp_fun_decl_id env) def.init

module Llbc = struct
  (** Pretty-printing for LLBC AST (generic functions) *)

  let pp_print_call = pp_call
  let pp_print_literal = pp_literal
  let pp_print_place = pp_place
  let pp_print_fn_ptr = pp_fn_ptr
  let pp_print_rvalue = pp_rvalue
  let pp_print_assertion = pp_assertion
  let pp_print_abort_kind = pp_abort_kind

  open LlbcAst

  let rec pp_statement (env : fmt_env) (indent : string) (indent_incr : string)
      (fmt : Format.formatter) (st : statement) : unit =
    List.iter
      (fun line -> Format.fprintf fmt "%s// %s\n" indent line)
      st.comments_before;
    pp_statement_kind env indent indent_incr fmt st.kind

  and pp_statement_kind (env : fmt_env) (indent : string) (indent_incr : string)
      (fmt : Format.formatter) (st : statement_kind) : unit =
    match st with
    | Assign (p, rv) ->
        Format.fprintf fmt "%s%a = %a" indent (pp_print_place env) p
          (pp_print_rvalue env) rv
    | SetDiscriminant (p, variant_id) ->
        Format.fprintf fmt "%s@discriminant(%s) = %s" indent
          (place_to_string env p)
          (VariantId.to_string variant_id)
    | CopyNonOverlapping { src; dst; count } ->
        Format.fprintf fmt "%scopy_nonoverlapping(%s, %s, %s)" indent
          (operand_to_string env src)
          (operand_to_string env dst)
          (operand_to_string env count)
    | StorageLive var_id ->
        Format.fprintf fmt "%sstorage_live(%s)" indent
          (local_id_to_string env var_id)
    | StorageDead var_id ->
        Format.fprintf fmt "%sstorage_dead(%s)" indent
          (local_id_to_string env var_id)
    | PlaceMention place ->
        Format.fprintf fmt "%s_ = %s" indent (place_to_string env place)
    | Drop (p, fn_ptr, kind) ->
        let kind =
          match kind with
          | Precise -> "drop"
          | Conditional -> "conditional_drop"
        in
        Format.fprintf fmt "%s%s[%a] %s" indent kind (pp_print_fn_ptr env)
          fn_ptr (place_to_string env p)
    | Assert (asrt, abort_kind) ->
        Format.fprintf fmt "%s%a else %a" indent (pp_print_assertion env) asrt
          (pp_print_abort_kind env) abort_kind
    | Call call -> pp_print_call env indent fmt call
    | Abort kind ->
        Format.fprintf fmt "%s%a" indent (pp_print_abort_kind env) kind
    | Return -> Format.fprintf fmt "%sreturn" indent
    | Break i -> Format.fprintf fmt "%sbreak %d" indent i
    | Continue i -> Format.fprintf fmt "%scontinue %d" indent i
    | Nop -> Format.fprintf fmt "%snop" indent
    | Switch switch -> (
        match switch with
        | If (op, true_st, false_st) ->
            let op = operand_to_string env op in
            let inner_indent = indent ^ indent_incr in
            Format.fprintf fmt "%sif %s {\n%a%s} else {\n%a%s}" indent op
              (pp_block env inner_indent indent_incr)
              true_st indent
              (pp_block env inner_indent indent_incr)
              false_st indent
        | SwitchInt (op, _ty, branches, otherwise) ->
            let op = operand_to_string env op in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            Format.fprintf fmt "%sswitch %s {\n" indent op;
            let first = ref true in
            List.iter
              (fun (svl, be) ->
                if !first then first := false else pp_string fmt "\n";
                Format.fprintf fmt "%s%a => {\n%a%s}," indent1
                  (pp_sep_list " | " pp_print_literal)
                  svl
                  (pp_block env indent2 indent_incr)
                  be indent1)
              branches;
            if not !first then pp_string fmt "\n";
            Format.fprintf fmt "%s_ => {\n%a%s},\n%s}" indent1
              (pp_block env indent2 indent_incr)
              otherwise indent1 indent
        | Match (place, branches, otherwise) ->
            let p = place_to_string env place in
            let discr_type =
              match place.ty with
              | TAdt { id = TAdtId type_id; _ } -> Some type_id
              | _ -> None
            in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            Format.fprintf fmt "%smatch %s {\n" indent p;
            let first = ref true in
            let pp_variant_id fmt variant_id =
              match discr_type with
              | Some type_id -> pp_adt_variant env type_id fmt variant_id
              | None -> pp_string fmt (variant_id_to_pretty_string variant_id)
            in
            List.iter
              (fun (svl, be) ->
                if !first then first := false else pp_string fmt "\n";
                Format.fprintf fmt "%s%a => {\n%a%s}," indent1
                  (pp_sep_list " | " pp_variant_id)
                  svl
                  (pp_block env indent2 indent_incr)
                  be indent1)
              branches;
            Option.iter
              (fun otherwise ->
                if not !first then pp_string fmt "\n";
                first := false;
                Format.fprintf fmt "%s_ => {\n%a%s}," indent1
                  (pp_block env indent2 indent_incr)
                  otherwise indent1)
              otherwise;
            Format.fprintf fmt "\n%s}" indent)
    | Loop loop_blk ->
        Format.fprintf fmt "%sloop {\n%a%s}" indent
          (pp_block env (indent ^ indent_incr) indent_incr)
          loop_blk indent
    | Error s -> Format.fprintf fmt "%sERROR(' %s')" indent s

  and pp_block (env : fmt_env) (indent : string) (indent_incr : string)
      (fmt : Format.formatter) (b : block) : unit =
    match b.statements with
    | [] -> ()
    | st :: statements ->
        pp_statement env indent indent_incr fmt st;
        List.iter
          (fun st ->
            pp_string fmt "\n";
            pp_statement env indent indent_incr fmt st)
          statements;
        pp_string fmt "\n"
end

module Ullbc = struct
  let pp_print_call = pp_call
  let pp_print_literal = pp_literal
  let pp_print_place = pp_place
  let pp_print_rvalue = pp_rvalue
  let pp_print_assertion = pp_assertion
  let pp_print_abort_kind = pp_abort_kind

  open UllbcAst

  let rec pp_statement (env : fmt_env) (indent : string)
      (fmt : Format.formatter) (st : statement) : unit =
    pp_statement_kind env indent fmt st.kind

  and pp_statement_kind (env : fmt_env) (indent : string)
      (fmt : Format.formatter) (st : statement_kind) : unit =
    match st with
    | Assign (p, rv) ->
        Format.fprintf fmt "%s%a := %a" indent (pp_print_place env) p
          (pp_print_rvalue env) rv
    | SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id
           (we are missing the def id here) *)
        Format.fprintf fmt "%sset_discriminant(%s, %s)" indent
          (place_to_string env p)
          (variant_id_to_pretty_string variant_id)
    | Assert (asrt, abort_kind) ->
        Format.fprintf fmt "%s%a else %a" indent (pp_print_assertion env) asrt
          (pp_print_abort_kind env) abort_kind
    | StorageLive var_id ->
        Format.fprintf fmt "%sstorage_live %s" indent
          (local_id_to_string env var_id)
    | StorageDead var_id ->
        Format.fprintf fmt "%sstorage_dead %s" indent
          (local_id_to_string env var_id)
    | PlaceMention place ->
        Format.fprintf fmt "%s_ := %s" indent (place_to_string env place)
    | CopyNonOverlapping { src; dst; count } ->
        Format.fprintf fmt "%scopy_non_overlapping(%s, %s, %s)" indent
          (operand_to_string env src)
          (operand_to_string env dst)
          (operand_to_string env count)
    | Nop -> pp_string fmt "nop"

  let pp_switch (indent : string) (fmt : Format.formatter) (tgt : switch) : unit
      =
    match tgt with
    | If (b0, b1) ->
        Format.fprintf fmt "%s[true -> %s; false -> %s]" indent
          (block_id_to_string b0) (block_id_to_string b1)
    | SwitchInt (_int_ty, branches, otherwise) ->
        Format.fprintf fmt "%s[" indent;
        List.iter
          (fun (sv, bid) ->
            Format.fprintf fmt "%a -> %s; " pp_print_literal sv
              (block_id_to_string bid))
          branches;
        Format.fprintf fmt "_ -> %s]" (block_id_to_string otherwise)

  let rec pp_terminator (env : fmt_env) (indent : string)
      (fmt : Format.formatter) (st : terminator) : unit =
    pp_terminator_kind env indent fmt st.kind

  and pp_terminator_kind (env : fmt_env) (indent : string)
      (fmt : Format.formatter) (st : terminator_kind) : unit =
    match st with
    | Goto bid -> Format.fprintf fmt "%sgoto %s" indent (block_id_to_string bid)
    | Switch (op, tgts) ->
        Format.fprintf fmt "%sswitch %s%a" indent (operand_to_string env op)
          (pp_switch indent) tgts
    | Call (call, tgt, unwind) ->
        Format.fprintf fmt "%a -> %s(unwind:%s)" (pp_print_call env indent) call
          (block_id_to_string tgt)
          (block_id_to_string unwind)
    | Drop (_, p, _, tgt, unwind) ->
        Format.fprintf fmt "%sdrop %s -> %s(unwind:%s)" indent
          (place_to_string env p) (block_id_to_string tgt)
          (block_id_to_string unwind)
    | TAssert (asrt, tgt, unwind) ->
        Format.fprintf fmt "%s%a -> %s(unwind:%s)" indent
          (pp_print_assertion env) asrt (block_id_to_string tgt)
          (block_id_to_string unwind)
    | Abort _ -> Format.fprintf fmt "%spanic" indent
    | Return -> Format.fprintf fmt "%sreturn" indent
    | UnwindResume -> Format.fprintf fmt "%sunwind_continue" indent

  let pp_block (env : fmt_env) (indent : string) (indent_incr : string)
      (fmt : Format.formatter) (id : BlockId.id) (block : block) : unit =
    let indent1 = indent ^ indent_incr in
    Format.fprintf fmt "%s%s {\n" indent (block_id_to_string id);
    List.iter
      (fun st -> Format.fprintf fmt "%a;\n" (pp_statement env indent1) st)
      block.statements;
    Format.fprintf fmt "%a;\n%s}"
      (pp_terminator env indent1)
      block.terminator indent

  let pp_blocks (env : fmt_env) (indent : string) (indent_incr : string)
      (fmt : Format.formatter) (blocks : block list) : unit =
    blocks
    |> BlockId.mapi (fun id block -> (id, block))
    |> pp_sep_list "\n\n"
         (fun fmt (id, block) -> pp_block env indent indent_incr fmt id block)
         fmt
end

let pp_llbc_block (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (body : LlbcAst.block) : unit =
  Llbc.pp_block env indent indent_incr fmt body

let pp_ullbc_block (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (id : UllbcAst.BlockId.id) (block : UllbcAst.block)
    : unit =
  Ullbc.pp_block env indent indent_incr fmt id block

let pp_ullbc_blocks (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (blocks : UllbcAst.block list) : unit =
  Ullbc.pp_blocks env indent indent_incr fmt blocks

let pp_fun_decl (env : fmt_env) (indent : string) (indent_incr : string)
    (fmt : Format.formatter) (def : fun_decl) : unit =
  let keyword = if def.signature.is_unsafe then "unsafe fn" else "fn" in
  let intro =
    item_intro_to_string env indent keyword (IdFun def.def_id) def.item_meta
  in
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr def.generics
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in
  let n_args = List.length def.signature.inputs in
  let args_of_locals (locals : locals) =
    locals.locals |> List.tl
    |> Collections.List.prefix n_args
    |> List.map local_to_string
  in
  let arg_names =
    match def.body with
    | StructuredBody { locals; _ } | UnstructuredBody { locals; _ } ->
        args_of_locals locals
    | IntrinsicBody (_, arg_names) ->
        arg_names
        |> Collections.List.mapi (fun i name ->
               let id = LocalId.of_int (i + 1) in
               match name with
               | Some name -> name ^ "_" ^ LocalId.to_string id
               | None -> "_" ^ LocalId.to_string id)
    | ErrorBody _
    | ExternBody _
    | MissingBody
    | OpaqueBody
    | TraitMethodWithoutDefaultBody
    | TargetDispatchBody _ ->
        List.init n_args (fun i -> "_" ^ string_of_int (i + 1))
  in
  let args = List.combine def.signature.inputs arg_names in
  Format.fprintf fmt "%s%s(" intro params;
  pp_sep_list ", "
    (fun fmt (ty, name) ->
      Format.fprintf fmt "%s: %s" name (ty_to_string env ty))
    fmt args;
  pp_string fmt ")";
  if not (ty_is_unit def.signature.output) then
    Format.fprintf fmt " -> %s" (ty_to_string env def.signature.output);
  pp_string fmt clauses;
  match def.body with
  | StructuredBody { locals; body; _ } ->
      let env_locals = List.map (fun v -> (v.index, v.name)) locals.locals in
      let env = { env with locals = env_locals } in
      let body_indent = indent ^ indent_incr in
      Format.fprintf fmt "\n%s{\n%a\n\n%a%s}" indent
        (pp_locals env body_indent)
        locals
        (pp_llbc_block env body_indent indent_incr)
        body indent
  | UnstructuredBody { locals; body; _ } ->
      let env_locals = List.map (fun v -> (v.index, v.name)) locals.locals in
      let env = { env with locals = env_locals } in
      let body_indent = indent ^ indent_incr in
      Format.fprintf fmt "\n%s{\n%a\n\n%a\n%s}" indent
        (pp_locals env body_indent)
        locals
        (pp_ullbc_blocks env body_indent indent_incr)
        body indent
  | TraitMethodWithoutDefaultBody ->
      Format.fprintf fmt "\n%s= <method_without_default_body>" indent
  | ExternBody name -> Format.fprintf fmt "\n%s= <extern:%s>" indent name
  | IntrinsicBody (name, _) ->
      Format.fprintf fmt "\n%s= <intrinsic:%s>" indent name
  | OpaqueBody -> Format.fprintf fmt "\n%s= <opaque>" indent
  | MissingBody -> Format.fprintf fmt "\n%s= <missing>" indent
  | ErrorBody error -> Format.fprintf fmt "\n%s= error(\"%s\")" indent error.msg
  | TargetDispatchBody targets ->
      let body_indent = indent ^ indent_incr in
      Format.fprintf fmt "\n%s= target_dispatch {\n" indent;
      List.iter
        (fun (target, fdecl) ->
          Format.fprintf fmt "%s%s => %a,\n" body_indent target
            (pp_fun_decl_ref env) fdecl)
        targets;
      Format.fprintf fmt "%s}" indent

let crate_to_fmt_env (crate : crate) : fmt_env =
  { crate; generics = []; locals = [] }

let pp_crate (fmt : Format.formatter) (m : crate) : unit =
  let env : fmt_env = crate_to_fmt_env m in
  let first = ref true in
  let emit (pp : Format.formatter -> unit) : unit =
    if !first then first := false else pp_string fmt "\n\n";
    pp fmt
  in
  let emit_string s = emit (fun fmt -> pp_string fmt s) in
  let format_item (id : item_id) : unit =
    match id with
    | IdType id -> (
        match TypeDeclId.Map.find_opt id m.type_decls with
        | Some d -> emit (fun fmt -> pp_type_decl env fmt d)
        | None ->
            emit_string ("Missing decl: " ^ item_id_to_pretty_string (IdType id))
        )
    | IdGlobal id -> (
        match GlobalDeclId.Map.find_opt id m.global_decls with
        | Some d -> emit (fun fmt -> pp_global_decl env "" tab_incr fmt d)
        | None ->
            emit_string
              ("Missing decl: " ^ item_id_to_pretty_string (IdGlobal id)))
    | IdTraitDecl id -> (
        match TraitDeclId.Map.find_opt id m.trait_decls with
        | Some d -> emit (fun fmt -> pp_trait_decl env "" tab_incr fmt d)
        | None ->
            emit_string
              ("Missing decl: " ^ item_id_to_pretty_string (IdTraitDecl id)))
    | IdTraitImpl id -> (
        match TraitImplId.Map.find_opt id m.trait_impls with
        | Some d -> emit (fun fmt -> pp_trait_impl env "" tab_incr fmt d)
        | None ->
            emit_string
              ("Missing decl: " ^ item_id_to_pretty_string (IdTraitImpl id)))
    | IdFun id -> (
        match FunDeclId.Map.find_opt id m.fun_decls with
        | Some d -> emit (fun fmt -> pp_fun_decl env "" tab_incr fmt d)
        | None ->
            emit_string ("Missing decl: " ^ item_id_to_pretty_string (IdFun id))
        )
  in
  let ids_of_group = function
    | NonRecGroup id -> [ id ]
    | RecGroup ids -> ids
  in
  if m.declarations = [] then (
    TypeDeclId.Map.iter
      (fun _ d -> emit (fun fmt -> pp_type_decl env fmt d))
      m.type_decls;
    GlobalDeclId.Map.iter
      (fun _ d -> emit (fun fmt -> pp_global_decl env "" tab_incr fmt d))
      m.global_decls;
    TraitDeclId.Map.iter
      (fun _ d -> emit (fun fmt -> pp_trait_decl env "" tab_incr fmt d))
      m.trait_decls;
    TraitImplId.Map.iter
      (fun _ d -> emit (fun fmt -> pp_trait_impl env "" tab_incr fmt d))
      m.trait_impls;
    FunDeclId.Map.iter
      (fun _ d -> emit (fun fmt -> pp_fun_decl env "" tab_incr fmt d))
      m.fun_decls)
  else
    m.declarations
    |> List.iter (function
         | TypeGroup g ->
             List.iter (fun id -> format_item (IdType id)) (ids_of_group g)
         | FunGroup g ->
             List.iter (fun id -> format_item (IdFun id)) (ids_of_group g)
         | GlobalGroup g ->
             List.iter (fun id -> format_item (IdGlobal id)) (ids_of_group g)
         | TraitDeclGroup g ->
             List.iter (fun id -> format_item (IdTraitDecl id)) (ids_of_group g)
         | TraitImplGroup g ->
             List.iter (fun id -> format_item (IdTraitImpl id)) (ids_of_group g)
         | MixedGroup g -> List.iter format_item (ids_of_group g));
  if not !first then pp_string fmt "\n\n"
