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

let integer_type_to_string = function
  | Signed Isize -> "isize"
  | Signed I8 -> "i8"
  | Signed I16 -> "i16"
  | Signed I32 -> "i32"
  | Signed I64 -> "i64"
  | Signed I128 -> "i128"
  | Unsigned Usize -> "usize"
  | Unsigned U8 -> "u8"
  | Unsigned U16 -> "u16"
  | Unsigned U32 -> "u32"
  | Unsigned U64 -> "u64"
  | Unsigned U128 -> "u128"

let float_type_to_string = function
  | F16 -> "f16"
  | F32 -> "f32"
  | F64 -> "f64"
  | F128 -> "f128"

let literal_type_to_string (ty : literal_type) : string =
  match ty with
  | TInt ity -> integer_type_to_string (Signed ity)
  | TUInt uty -> integer_type_to_string (Unsigned uty)
  | TFloat fty -> float_type_to_string fty
  | TBool -> "bool"
  | TChar -> "char"

let big_int_to_string (bi : big_int) : string = Z.to_string bi

let scalar_value_to_string (sv : scalar_value) : string =
  big_int_to_string (Scalars.get_val sv)
  ^ " : "
  ^ integer_type_to_string (Scalars.get_ty sv)

let float_value_to_string (fv : float_value) : string =
  fv.float_value ^ " : " ^ float_type_to_string fv.float_ty

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

let literal_to_string (lit : literal) : string =
  match lit with
  | VScalar sv -> scalar_value_to_string sv
  | VFloat fv -> float_value_to_string fv
  | VBool b -> Bool.to_string b
  | VChar c -> uchar_to_utf8 c
  | VStr s -> "\"" ^ escape_string s ^ "\""
  | VByteStr bs -> "[" ^ String.concat ", " (List.map string_of_int bs) ^ "]"

let g_region_group_to_string (rid_to_string : 'rid -> string)
    (id_to_string : 'id -> string) (gr : ('rid, 'id) g_region_group) : string =
  let { id; regions; parents } = gr in
  "{ id: " ^ id_to_string id ^ "; regions: ["
  ^ String.concat ", " (List.map rid_to_string regions)
  ^ "]; parents: ["
  ^ String.concat ", " (List.map id_to_string parents)
  ^ "] }"

let region_var_group_to_string (gr : region_var_group) : string =
  g_region_group_to_string RegionId.to_string RegionGroupId.to_string gr

let region_var_groups_to_string (gl : region_var_groups) : string =
  String.concat "\n" (List.map region_var_group_to_string gl)

let ref_kind_to_string (rk : ref_kind) : string =
  match rk with
  | RMut -> "Mut"
  | RShared -> "Shared"

let builtin_ty_to_string (_ : builtin_ty) : string = "Box"

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

let region_binder_to_string (value_to_string : fmt_env -> 'c -> string)
    (env : fmt_env) (rb : 'c region_binder) : string =
  let env = fmt_env_push_regions env rb.binder_regions in
  let value = value_to_string env rb.binder_value in
  match rb.binder_regions with
  | [] -> value
  | _ ->
      "for<"
      ^ String.concat ", "
          (List.map (region_param_to_string env) rb.binder_regions)
      ^ "> " ^ value

let rec type_id_to_string (env : fmt_env) (id : type_id) : string =
  match id with
  | TAdtId id -> type_decl_id_to_string env id
  | TTuple -> ""
  | TBuiltin aty -> (
      match aty with
      | TBox -> "alloc::boxed::Box"
      | TStr -> "Str")

and type_decl_id_to_string env def_id =
  match find_short_name env (IdType def_id) with
  | Some name -> name_to_string env name
  | None -> type_decl_id_to_pretty_string def_id

and type_decl_ref_to_string (env : fmt_env) (tref : type_decl_ref) : string =
  match tref.id with
  | TTuple ->
      let params, _trait_refs = generic_args_to_strings env tref.generics in
      let trailing_comma = if List.length params = 1 then "," else "" in
      "(" ^ String.concat ", " params ^ trailing_comma ^ ")"
  | id ->
      let id = type_id_to_string env id in
      let generics = generic_args_to_string env tref.generics in
      id ^ generics

and fun_decl_id_to_string (env : fmt_env) (id : FunDeclId.id) : string =
  match find_short_name env (IdFun id) with
  | Some name -> name_to_string env name
  | None -> fun_decl_id_to_pretty_string id

and fun_decl_ref_to_string (env : fmt_env) (fn : fun_decl_ref) : string =
  let fun_id = fun_decl_id_to_string env fn.id in
  let generics = generic_args_to_string_for_fn env fn.generics in
  fun_id ^ generics

and global_decl_id_to_string env def_id =
  match find_short_name env (IdGlobal def_id) with
  | Some name -> name_to_string env name
  | None -> global_decl_id_to_pretty_string def_id

and global_decl_ref_to_string (env : fmt_env) (gr : global_decl_ref) : string =
  let global_id = global_decl_id_to_string env gr.id in
  let generics = generic_args_to_string env gr.generics in
  global_id ^ generics

and trait_decl_id_to_string env id =
  match find_short_name env (IdTraitDecl id) with
  | Some name -> name_to_string env name
  | None -> trait_decl_id_to_pretty_string id

and trait_impl_id_to_string env id =
  match find_short_name env (IdTraitImpl id) with
  | Some name -> name_to_string env name
  | None -> trait_impl_id_to_pretty_string id

and trait_impl_ref_to_string (env : fmt_env) (iref : trait_impl_ref) : string =
  let impl = trait_impl_id_to_string env iref.id in
  let generics = generic_args_to_string env iref.generics in
  impl ^ generics

and provenance_to_string (env : fmt_env) (pv : provenance) : string =
  match pv with
  | ProvGlobal gref -> "prov_global(" ^ global_decl_ref_to_string env gref ^ ")"
  | ProvFunction fn_ref -> "prov_fn(" ^ fun_decl_ref_to_string env fn_ref ^ ")"
  | ProvUnknown -> "prov_unknown"

and byte_to_string (env : fmt_env) (cv : byte) : string =
  match cv with
  | Uninit -> "--"
  | Value b -> Printf.sprintf "%#4x" b
  | Provenance (p, i) ->
      provenance_to_string env p ^ "[" ^ string_of_int i ^ "]"

and unsizing_metadata_to_string (env : fmt_env) (meta : unsizing_metadata) :
    string =
  match meta with
  | MetaLength len -> constant_expr_to_string env len
  | MetaVTable (_, vtable) -> constant_expr_to_string env vtable
  | MetaVTableUpcast fields ->
      " at [" ^ String.concat ", " (List.map FieldId.to_string fields) ^ "]"
  | MetaUnknown -> "?"

and const_aggregate_to_string (env : fmt_env) (tref : type_decl_ref)
    opt_variant_id (fields : constant_expr list) : string =
  let fields = List.map (constant_expr_to_string env) fields in

  match tref.id with
  | TTuple ->
      let trailing_comma = if List.length fields = 1 then "," else "" in
      "(" ^ String.concat ", " fields ^ trailing_comma ^ ")"
  | TAdtId def_id ->
      let variant_name =
        match opt_variant_id with
        | None -> type_decl_id_to_string env def_id
        | Some variant_id -> adt_variant_to_string env def_id variant_id
      in
      let fields =
        match adt_field_names env def_id opt_variant_id with
        | None ->
            fields
            |> List.mapi (fun i value ->
                   FieldId.to_string (FieldId.of_int i) ^ ": " ^ value)
        | Some field_names ->
            let fields = List.combine field_names fields in
            let fields =
              List.map (fun (field, value) -> field ^ ": " ^ value) fields
            in
            fields
      in
      variant_name ^ " { " ^ String.concat ", " fields ^ " }"
  | TBuiltin _ -> raise (Failure "Unreachable")

and constant_expr_to_string (env : fmt_env) (cv : constant_expr) : string =
  match cv.kind with
  | CLiteral lit -> literal_to_string lit
  | CVar var -> const_generic_db_var_to_string env var
  | CTraitConst (trait_ref, const_id) ->
      let name =
        GAstUtils.get_assoc_const_name env.crate
          trait_ref.trait_decl_ref.binder_value.id const_id
      in
      let trait_ref = trait_ref_to_string env trait_ref in
      trait_ref ^ "::" ^ name
  | CVTableRef trait_ref ->
      let trait_ref = trait_ref_to_string env trait_ref in
      "&vtable_of(" ^ trait_ref ^ ")"
  | CFnDef fn_ptr -> fn_ptr_to_string env fn_ptr
  | CFnPtr fn_ptr -> "fnptr(" ^ fn_ptr_to_string env fn_ptr ^ ")"
  | CRawMemory bytes ->
      "RawMemory("
      ^ String.concat ", " (List.map (byte_to_string env) bytes)
      ^ ")"
  | COpaque reason -> "Opaque(" ^ reason ^ ")"
  | CAdt (variant_id, fields) -> begin
      match cv.ty with
      | TAdt tref -> const_aggregate_to_string env tref variant_id fields
      | _ -> "malformed constant"
    end
  | CArray fields ->
      "["
      ^ String.concat ", " (List.map (constant_expr_to_string env) fields)
      ^ "]"
  | CGlobal gref -> global_decl_ref_to_string env gref
  | CPtrNoProvenance n -> "no-provenance " ^ Z.to_string n
  | CRef (c, meta) ->
      let c = constant_expr_to_string env c in
      begin
        match meta with
        | None -> "&" ^ c
        | Some meta ->
            "&" ^ c ^ " with_metadata("
            ^ unsizing_metadata_to_string env meta
            ^ ")"
      end
  | CPtr (ref_kind, c, meta) ->
      let ref_kind =
        match ref_kind with
        | RShared -> "&raw const"
        | RMut -> "&raw mut"
      in
      let c = constant_expr_to_string env c in
      begin
        match meta with
        | None -> ref_kind ^ " " ^ c
        | Some meta ->
            ref_kind ^ " " ^ c ^ " with_metadata("
            ^ unsizing_metadata_to_string env meta
            ^ ")"
      end

and builtin_fun_id_to_string (aid : builtin_fun_id) : string =
  match aid with
  | BoxNew -> "BoxNew"
  | ArrayToSliceShared -> "ArrayToSliceShared"
  | ArrayToSliceMut -> "ArrayToSliceMut"
  | ArrayRepeat -> "ArrayRepeat"
  | Index { is_array; mutability; is_range } ->
      let ty = if is_array then "Array" else "Slice" in
      let op = if is_range then "SubSlice" else "Index" in
      let mutability = ref_kind_to_string mutability in
      ty ^ op ^ mutability
  | PtrFromParts mut ->
      let mut = ref_kind_to_string mut in
      "PtrFromParts" ^ mut

and fun_id_to_string (env : fmt_env) (fid : fun_id) : string =
  match fid with
  | FRegular fid -> fun_decl_id_to_string env fid
  | FBuiltin aid -> "@" ^ builtin_fun_id_to_string aid

and fn_ptr_kind_to_string (env : fmt_env) (r : fn_ptr_kind) : string =
  match r with
  | TraitMethod (trait_ref, method_id, _) ->
      let method_name =
        GAstUtils.get_method_name env.crate
          trait_ref.trait_decl_ref.binder_value.id method_id
      in
      trait_ref_to_string env trait_ref ^ "::" ^ method_name
  | FunId fid -> fun_id_to_string env fid

and fn_ptr_to_string (env : fmt_env) (ptr : fn_ptr) : string =
  let generics = generic_args_to_string_for_fn env ptr.generics in
  fn_ptr_kind_to_string env ptr.kind ^ generics

and ty_to_string (env : fmt_env) (ty : ty) : string =
  match ty with
  | TAdt tref -> type_decl_ref_to_string env tref
  | TVar tv -> type_db_var_to_string env tv
  | TNever -> "!"
  | TLiteral lit_ty -> literal_type_to_string lit_ty
  | TTraitType (trait_ref, type_id) ->
      let type_name =
        GAstUtils.get_assoc_type_name env.crate
          trait_ref.trait_decl_ref.binder_value.id type_id
      in
      trait_ref_to_string env trait_ref ^ "::" ^ type_name
  | TRef (r, rty, ref_kind) -> (
      match ref_kind with
      | RMut -> "&" ^ region_to_string env r ^ " mut " ^ ty_to_string env rty
      | RShared -> "&" ^ region_to_string env r ^ " " ^ ty_to_string env rty)
  | TRawPtr (rty, ref_kind) -> (
      match ref_kind with
      | RMut -> "*mut " ^ ty_to_string env rty
      | RShared -> "*const " ^ ty_to_string env rty)
  | TFnPtr binder ->
      let env = fmt_env_push_regions env binder.binder_regions in
      let { inputs; output; is_unsafe } = binder.binder_value in
      let unsafe = if is_unsafe then "unsafe " else "" in
      let regions =
        match binder.binder_regions with
        | [] -> ""
        | regions ->
            "<"
            ^ String.concat ", " (List.map (region_param_to_string env) regions)
            ^ ">"
      in
      let inputs =
        "(" ^ String.concat ", " (List.map (ty_to_string env) inputs) ^ ")"
      in
      let output =
        if ty_is_unit output then "" else " -> " ^ ty_to_string env output
      in
      unsafe ^ "fn" ^ regions ^ inputs ^ output
  | TFnDef f ->
      let env = fmt_env_push_regions env f.binder_regions in
      let regions =
        match f.binder_regions with
        | [] -> ""
        | regions ->
            "for<"
            ^ String.concat ", " (List.map (region_param_to_string env) regions)
            ^ "> "
      in
      let fn = fn_ptr_to_string env f.binder_value in
      regions ^ fn
  | TDynTrait pred -> "(dyn " ^ dyn_predicate_to_string env pred ^ ")"
  | TArray (ty, len) ->
      "[" ^ ty_to_string env ty ^ "; " ^ constant_expr_to_string env len ^ "]"
  | TSlice ty -> "[" ^ ty_to_string env ty ^ "]"
  | TPtrMetadata ty -> "PtrMetadata<" ^ ty_to_string env ty ^ ">"
  | TError msg -> "type_error(\"" ^ msg ^ "\")"

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

and dyn_trait_clause_to_string (env : fmt_env)
    (constraints : (trait_clause_id * string list) list) (clause : trait_param)
    : string =
  let clause_constraints =
    match List.assoc_opt clause.clause_id constraints with
    | None -> []
    | Some constraints -> constraints
  in
  let fmt_trait env (tr : trait_decl_ref) =
    let trait_id = trait_decl_id_to_string env tr.id in
    let generics =
      match tr.generics.types with
      | _self_ty :: types -> { tr.generics with types }
      | [] -> tr.generics
    in
    let params, _trait_refs = generic_args_to_strings env generics in
    let params = params @ clause_constraints in
    let params =
      if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
    in
    trait_id ^ params
  in
  region_binder_to_string fmt_trait env clause.trait

and dyn_types_outlive_to_string (env : fmt_env)
    (rb : (ty, region) outlives_pred region_binder) : string option =
  match rb.binder_value with
  | _, RErased -> None
  | _, region ->
      Some
        (region_binder_to_string
           (fun env (_, region) -> region_to_string env region)
           env rb)

and dyn_predicate_to_string (env : fmt_env) (pred : dyn_predicate) : string =
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
  String.concat " + " (trait_clauses @ types_outlive)

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

and generic_args_to_string (env : fmt_env) (generics : generic_args) : string =
  let params, trait_refs = generic_args_to_strings env generics in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in
  let trait_refs =
    if trait_refs = [] then "" else "[" ^ String.concat ", " trait_refs ^ "]"
  in
  params ^ trait_refs

and generic_args_to_string_for_fn (env : fmt_env) (generics : generic_args) :
    string =
  generic_args_to_string env generics

and trait_ref_kind_to_string (env : fmt_env)
    (implements : trait_decl_ref region_binder option) (kind : trait_ref_kind) :
    string =
  match kind with
  | Self -> "Self"
  | TraitImpl impl_ref -> trait_impl_ref_to_string env impl_ref
  | BuiltinOrAuto (_, _, types) ->
      let implements = Option.get implements in
      let impl =
        region_binder_to_string trait_decl_ref_as_impl_to_string env implements
      in
      let types =
        AssocTypeId.Map.to_list types
        |> List.map (fun (type_id, (assoc_ty : trait_assoc_ty_impl)) ->
               let name =
                 GAstUtils.get_assoc_type_name env.crate
                   implements.binder_value.id type_id
               in
               name ^ "  = " ^ ty_to_string env assoc_ty.value)
      in
      let types =
        if types = [] then "" else " where " ^ String.concat ", " types
      in
      "{built_in impl " ^ impl ^ types ^ "}"
  | Clause id -> trait_db_var_to_string env id
  | ParentClause (tref, clause_id) ->
      let inst_id = trait_ref_to_string env tref in
      inst_id ^ "::parent_clause" ^ TraitClauseId.to_string clause_id
  | ItemClause (tref, type_id, clause_id) ->
      let inst_id = trait_ref_to_string env tref in
      let type_name =
        GAstUtils.get_assoc_type_name env.crate
          tref.trait_decl_ref.binder_value.id type_id
      in
      let clause_id = trait_clause_id_to_pretty_string clause_id in
      "(" ^ inst_id ^ "::" ^ type_name ^ "::[" ^ clause_id ^ "])"
  | Dyn ->
      let trait =
        region_binder_to_string trait_decl_ref_to_string env
          (Option.get implements)
      in
      trait
  | UnknownTrait msg -> "UNKNOWN(" ^ msg ^ ")"

and trait_ref_to_string (env : fmt_env) (tr : trait_ref) : string =
  trait_ref_kind_to_string env (Some tr.trait_decl_ref) tr.kind

and trait_decl_ref_to_string (env : fmt_env) (tr : trait_decl_ref) : string =
  let trait_id = trait_decl_id_to_string env tr.id in
  let generics = generic_args_to_string env tr.generics in
  trait_id ^ generics

and trait_decl_ref_as_impl_to_string (env : fmt_env) (tr : trait_decl_ref) :
    string =
  match tr.generics.types with
  | self_ty :: types ->
      let generics = { tr.generics with types } in
      let pred = trait_decl_ref_to_string env { tr with generics } in
      pred ^ " for " ^ ty_to_string env self_ty
  | [] -> trait_decl_ref_to_string env tr

and impl_elem_to_string (env : fmt_env) (elem : impl_elem) : string =
  match elem with
  | ImplElemTy bound_ty ->
      (* Locally replace the generics and the predicates *)
      let env = fmt_env_push_generics_and_preds env bound_ty.binder_params in
      ty_to_string env bound_ty.binder_value
  | ImplElemTrait impl_id -> begin
      match TraitImplId.Map.find_opt impl_id env.crate.trait_impls with
      | None -> "impl#" ^ TraitImplId.to_string impl_id
      | Some impl ->
          (* Locally replace the generics and the predicates *)
          let env = fmt_env_push_generics_and_preds env impl.generics in
          "impl " ^ trait_decl_ref_as_impl_to_string env impl.impl_trait
    end

and path_elem_to_string (env : fmt_env) (e : path_elem) : string =
  match e with
  | PeIdent (s, d) ->
      let d =
        if d = Disambiguator.zero then "" else "#" ^ Disambiguator.to_string d
      in
      s ^ d
  | PeImpl impl -> "{" ^ impl_elem_to_string env impl ^ "}"
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
      "<" ^ String.concat ", " explicits ^ ">"
  | PeTarget target -> target

and name_to_string (env : fmt_env) (n : name) : string =
  let env = { env with generics = [] } in
  let name = List.map (path_elem_to_string env) n in
  String.concat "::" name

and raw_attribute_to_string (attr : raw_attribute) : string =
  let args =
    match attr.args with
    | None -> ""
    | Some args -> "(" ^ args ^ ")"
  in
  attr.path ^ args

and trait_param_to_string (env : fmt_env) (clause : trait_param) : string =
  let clause_id = trait_clause_id_to_string_for_env env clause.clause_id in
  let trait =
    region_binder_to_string trait_decl_ref_to_string env clause.trait
  in
  "[" ^ clause_id ^ "]: " ^ trait

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

and adt_variant_to_string (env : fmt_env) (def_id : TypeDeclId.id)
    (variant_id : VariantId.id) : string =
  match TypeDeclId.Map.find_opt def_id env.crate.type_decls with
  | None ->
      type_decl_id_to_pretty_string def_id
      ^ "::"
      ^ variant_id_to_pretty_string variant_id
  | Some def -> begin
      match def.kind with
      | Enum variants ->
          let variant = VariantId.nth variants variant_id in
          type_decl_id_to_string env def_id ^ "::" ^ variant.variant_name
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

let field_to_string env (f : field) : string =
  match f.field_name with
  | Some field_name -> field_name ^ ": " ^ ty_to_string env f.field_ty
  | None -> ty_to_string env f.field_ty

let variant_to_string env (v : variant) : string =
  if v.fields = [] then v.variant_name
  else
    v.variant_name ^ "("
    ^ String.concat ", " (List.map (field_to_string env) v.fields)
    ^ ")"

let trait_type_constraint_to_string (env : fmt_env)
    (ttc : trait_type_constraint) : string =
  let { trait_ref; type_id; ty } = ttc in
  let type_name =
    GAstUtils.get_assoc_type_name env.crate
      trait_ref.trait_decl_ref.binder_value.id type_id
  in
  let trait_ref = trait_ref_to_string env trait_ref in
  let ty = ty_to_string env ty in
  trait_ref ^ "::" ^ type_name ^ " = " ^ ty

(** Helper to format "where" clauses *)
let clauses_to_string (indent : string) (indent_incr : string)
    (clauses : string list) : string =
  if clauses = [] then ""
  else
    let env_clause s = indent ^ indent_incr ^ s ^ "," in
    let clauses = List.map env_clause clauses in
    "\n" ^ indent ^ "where\n" ^ String.concat "\n" clauses

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

let generic_params_to_string_single_line (env : fmt_env)
    (generics : generic_params) : string =
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
  if all = [] then "" else "<" ^ String.concat ", " all ^ ">"

let item_intro_to_string (env : fmt_env) (indent : string) (keyword : string)
    (id : item_id) (meta : item_meta) : string =
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
  full_name_comment ^ lang_item ^ indent ^ public ^ keyword ^ " " ^ name

let type_decl_to_string (env : fmt_env) (def : type_decl) : string =
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
  (* Locally update the generics and the predicates *)
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
      let fields =
        if fields = [] then ""
        else
          "\n"
          ^ String.concat ""
              (List.map (fun f -> "  " ^ field_to_string env f ^ ",\n") fields)
      in
      intro ^ params ^ clauses ^ nl_or_space ^ "{" ^ fields ^ "}"
  | Enum variants ->
      let variants =
        "\n"
        ^ String.concat ""
            (List.map
               (fun v -> "  " ^ variant_to_string env v ^ ",\n")
               variants)
      in
      intro ^ params ^ clauses ^ nl_or_space ^ "{" ^ variants ^ "}"
  | Union fields ->
      let fields =
        "\n"
        ^ String.concat ""
            (List.map (fun f -> "  " ^ field_to_string env f ^ ",\n") fields)
      in
      intro ^ params ^ clauses ^ nl_or_space ^ "{" ^ fields ^ "}"
  | Alias ty -> intro ^ params ^ clauses ^ " = " ^ ty_to_string env ty
  | Opaque -> intro ^ params ^ clauses
  | TDeclError err -> intro ^ params ^ clauses ^ " = ERROR(" ^ err ^ ")"

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

let (var_id_to_pretty_string
     [@ocaml.alert deprecated "use [local_id_to_pretty_string] instead"]) =
  local_id_to_pretty_string

let (var_id_to_string
     [@ocaml.alert deprecated "use [local_id_to_string] instead"]) =
  local_id_to_string

let (var_to_string [@ocaml.alert deprecated "use [local_to_string] instead"]) =
  local_to_string

let rec projection_elem_to_string (env : fmt_env) (sub : string)
    (pe : projection_elem) : string =
  match pe with
  | Deref -> "(*" ^ sub ^ ")"
  | ProjIndex (off, from_end) ->
      let idx_pre = if from_end then "-" else "" in
      sub ^ "[" ^ idx_pre ^ operand_to_string env off ^ "]"
  | Subslice (from, to_, from_end) ->
      let to_ =
        if from_end then "-" ^ operand_to_string env to_
        else operand_to_string env to_
      in
      sub ^ "[" ^ operand_to_string env from ^ ".." ^ to_ ^ "]"
  | Field (ProjTuple _, fid) -> sub ^ "." ^ FieldId.to_string fid
  | Field (ProjAdt (adt_id, opt_variant_id), fid) -> (
      let field_name =
        match adt_field_to_string env adt_id opt_variant_id fid with
        | Some field_name -> field_name
        | None -> FieldId.to_string fid
      in
      match opt_variant_id with
      | None -> "(" ^ sub ^ ")." ^ field_name
      | Some variant_id ->
          let variant_name = adt_variant_to_string env adt_id variant_id in
          "(" ^ sub ^ " as variant " ^ variant_name ^ ")." ^ field_name)
  | PtrMetadata -> sub ^ ".metadata"

and place_to_string (env : fmt_env) (p : place) : string =
  match p.kind with
  | PlaceLocal var_id -> local_id_to_string env var_id
  | PlaceProjection (subplace, pe) ->
      let subplace = place_to_string env subplace in
      projection_elem_to_string env subplace pe
  | PlaceGlobal global_ref ->
      let generics = generic_args_to_string env global_ref.generics in
      global_decl_id_to_string env global_ref.id ^ generics

and cast_kind_to_string (env : fmt_env) (cast : cast_kind) : string =
  match cast with
  | CastScalar (src, tgt) ->
      "cast<" ^ literal_type_to_string src ^ ", " ^ literal_type_to_string tgt
      ^ ">"
  | CastFnPtr (src, tgt) | CastRawPtr (src, tgt) ->
      "cast<" ^ ty_to_string env src ^ ", " ^ ty_to_string env tgt ^ ">"
  | CastTransmute (src, tgt) ->
      "transmute<" ^ ty_to_string env src ^ ", " ^ ty_to_string env tgt ^ ">"
  | CastUnsize (src, tgt, meta) ->
      "unsize_cast<" ^ ty_to_string env src ^ ", " ^ ty_to_string env tgt ^ ", "
      ^ unsizing_metadata_to_string env meta
      ^ ">"
  | CastConcretize (src, tgt) ->
      "concretize<" ^ ty_to_string env src ^ ", " ^ ty_to_string env tgt ^ ">"

and nullop_to_string (env : fmt_env) (op : nullop) : string =
  match op with
  | SizeOf -> "size_of"
  | AlignOf -> "align_of"
  | OffsetOf (ty, opt_variant_id, field_id) ->
      let type_name = type_decl_ref_to_string env ty in
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
      "offset_of(" ^ type_name ^ "." ^ variant_name ^ field_name ^ ")"
  | UbChecks -> "ub_checks"
  | ContractChecks -> "contract_checks"
  | OverflowChecks -> "overflow_checks"

and unop_to_string (env : fmt_env) (unop : unop) : string =
  match unop with
  | Not -> "~"
  | Neg om -> overflow_mode_to_string om ^ ".-"
  | Cast cast_kind -> cast_kind_to_string env cast_kind

and overflow_mode_to_string (mode : overflow_mode) : string =
  match mode with
  | OWrap -> "wrap"
  | OUB -> "ub"
  | OPanic -> "panic"

and binop_to_string (binop : binop) : string =
  match binop with
  | BitXor -> "^"
  | BitAnd -> "&"
  | BitOr -> "|"
  | Eq -> "=="
  | Lt -> "<"
  | Le -> "<="
  | Ne -> "!="
  | Ge -> ">="
  | Gt -> ">"
  | Div om -> overflow_mode_to_string om ^ "./"
  | Rem om -> overflow_mode_to_string om ^ ".%"
  | Add om -> overflow_mode_to_string om ^ ".+"
  | Sub om -> overflow_mode_to_string om ^ ".-"
  | Mul om -> overflow_mode_to_string om ^ ".*"
  | Shl om -> overflow_mode_to_string om ^ ".<<"
  | Shr om -> overflow_mode_to_string om ^ ".>>"
  | AddChecked -> "checked.+"
  | SubChecked -> "checked.-"
  | MulChecked -> "checked.*"
  | Cmp -> "cmp"
  | Offset -> "offset"

and operand_to_string (env : fmt_env) (op : operand) : string =
  match op with
  | Copy p -> "copy " ^ place_to_string env p
  | Move p -> "move " ^ place_to_string env p
  | Constant cv -> "const " ^ constant_expr_to_string env cv

and operand_ty (op : operand) : ty =
  match op with
  | Copy p | Move p -> p.ty
  | Constant cv -> cv.ty

and aggregate_to_string (env : fmt_env) (agg : aggregate_kind)
    (fields : operand list) : string =
  let fields = List.map (operand_to_string env) fields in
  match agg with
  | AggregatedAdt (tref, opt_variant_id, opt_field_id) -> (
      match tref.id with
      | TTuple ->
          let trailing_comma = if List.length fields = 1 then "," else "" in
          "(" ^ String.concat ", " fields ^ trailing_comma ^ ")"
      | TBuiltin TBox -> "Box(" ^ String.concat ", " fields ^ ")"
      | TBuiltin TStr -> "[" ^ String.concat ", " fields ^ "]"
      | TAdtId def_id ->
          let variant_name =
            match opt_variant_id with
            | None -> type_decl_id_to_string env def_id
            | Some variant_id -> adt_variant_to_string env def_id variant_id
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
          variant_name ^ " { " ^ String.concat ", " fields ^ " }")
  | AggregatedArray (_ty, _cg) -> "[" ^ String.concat ", " fields ^ "]"
  | AggregatedRawPtr (_, refk) ->
      let refk =
        match refk with
        | RShared -> "const"
        | RMut -> "mut "
      in
      "*" ^ refk ^ " (" ^ String.concat ", " fields ^ ")"

and rvalue_to_string (env : fmt_env) (rv : rvalue) : string =
  match rv with
  | Use op -> operand_to_string env op
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
      if ty_is_unit (operand_ty op) then borrow_kind ^ p
      else borrow_kind ^ p ^ " with_metadata(" ^ operand_to_string env op ^ ")"
    end
  | RawPtr (p, pk, op) -> begin
      let p = place_to_string env p in
      let ptr_kind =
        match pk with
        | RShared -> "&raw const "
        | RMut -> "&raw mut "
      in
      if ty_is_unit (operand_ty op) then ptr_kind ^ p
      else ptr_kind ^ p ^ " with_metadata(" ^ operand_to_string env op ^ ")"
    end
  | NullaryOp (op, ty) ->
      nullop_to_string env op ^ "<" ^ ty_to_string env ty ^ ">"
  | UnaryOp (unop, op) ->
      unop_to_string env unop ^ "(" ^ operand_to_string env op ^ ")"
  | BinaryOp (binop, op1, op2) ->
      operand_to_string env op1 ^ " " ^ binop_to_string binop ^ " "
      ^ operand_to_string env op2
  | Discriminant p -> "@discriminant(" ^ place_to_string env p ^ ")"
  | Len (place, _, _) -> "len(" ^ place_to_string env place ^ ")"
  | Repeat (v, _, len) ->
      "[" ^ operand_to_string env v ^ "; "
      ^ constant_expr_to_string env len
      ^ "]"
  | Aggregate (akind, ops) -> aggregate_to_string env akind ops

let item_id_to_string (id : item_id) : string =
  match id with
  | IdFun id -> FunDeclId.to_string id
  | IdGlobal id -> GlobalDeclId.to_string id
  | IdType id -> TypeDeclId.to_string id
  | IdTraitDecl id -> TraitDeclId.to_string id
  | IdTraitImpl id -> TraitImplId.to_string id

let fn_operand_to_string (env : fmt_env) (op : fn_operand) : string =
  match op with
  | FnOpRegular func -> fn_ptr_to_string env func
  | FnOpDynamic op -> "(" ^ operand_to_string env op ^ ")"

let call_to_string (env : fmt_env) (indent : string) (call : call) : string =
  let func = fn_operand_to_string env call.func in
  let args = List.map (operand_to_string env) call.args in
  let args = "(" ^ String.concat ", " args ^ ")" in
  let dest = place_to_string env call.dest in
  indent ^ dest ^ " = " ^ func ^ args

let assertion_to_string (env : fmt_env) (a : assertion) : string =
  let cond = operand_to_string env a.cond in
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
  "assert(" ^ cond ^ " == " ^ Bool.to_string a.expected ^ ")" ^ check_kind

let abort_kind_to_string (env : fmt_env) (a : abort_kind) : string =
  match a with
  | Panic None -> "panic"
  | Panic (Some name) -> "panic(" ^ name_to_string env name ^ ")"
  | UndefinedBehavior -> "undefined_behavior"
  | UnwindTerminate -> "unwind_terminate"

(** Small helper *)
let fun_sig_with_name_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) (attribute : string option) (name : string option)
    (args : local list option) (sg : bound_fun_sig) : string =
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
  let args =
    match args with
    | None ->
        let args = List.map ty_to_string sg.inputs in
        String.concat ", " args
    | Some args ->
        let args = List.combine args sg.inputs in
        let args =
          List.map
            (fun (var, rty) -> local_to_string var ^ " : " ^ ty_to_string rty)
            args
        in
        String.concat ", " args
  in

  (* Put everything together *)
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
  indent ^ attribute ^ unsafe ^ "fn" ^ name ^ params ^ "(" ^ args ^ ")" ^ ret_ty
  ^ clauses

let fun_sig_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (sg : fun_sig item_binder) : string =
  fun_sig_with_name_to_string env indent indent_incr None None None sg

let locals_to_string (env : fmt_env) (indent : string) (locals : locals) :
    string =
  locals.locals
  |> List.map (fun var ->
         let kind =
           if var.index = LocalId.zero then "return"
           else if LocalId.to_int var.index <= locals.arg_count then
             "arg #" ^ LocalId.to_string var.index
           else
             match var.name with
             | Some _ -> "local"
             | None -> "anonymous local"
         in
         indent ^ "let " ^ local_to_string var ^ ": "
         ^ ty_to_string env var.local_ty
         ^ "; // " ^ kind)
  |> String.concat "\n"

let trait_decl_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) (def : trait_decl) : string =
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

  let items =
    let parent_clauses =
      List.map
        (fun clause ->
          indent1 ^ "parent_clause"
          ^ TraitClauseId.to_string clause.clause_id
          ^ " : "
          ^ trait_param_to_string env clause
          ^ "\n")
        def.implied_clauses
    in
    let consts =
      List.map
        (fun c ->
          let ty = ty_to_string env c.ty in
          indent1 ^ "const " ^ c.name ^ " : " ^ ty ^ "\n")
        (AssocConstId.Map.values def.consts)
    in
    let types =
      List.map
        (fun (bound_ty : trait_assoc_ty binder) ->
          let env =
            fmt_env_push_generics_and_preds env bound_ty.binder_params
          in
          let params =
            generic_params_to_string_single_line env bound_ty.binder_params
          in
          let implied_clauses =
            if bound_ty.binder_value.implied_clauses = [] then ""
            else
              "\n" ^ indent1 ^ "where\n"
              ^ String.concat ""
                  (List.map
                     (fun c ->
                       indent1 ^ indent_incr ^ "implied_clause_"
                       ^ TraitClauseId.to_string c.clause_id
                       ^ " : "
                       ^ trait_param_to_string env c
                       ^ "\n")
                     bound_ty.binder_value.implied_clauses)
          in
          indent1 ^ "type " ^ bound_ty.binder_value.name ^ params
          ^ implied_clauses ^ "\n")
        (AssocTypeId.Map.values def.types)
    in
    let methods =
      List.map
        (fun (m : trait_method binder) ->
          let env = fmt_env_push_generics_and_preds env m.binder_params in
          let params =
            generic_params_to_string_single_line env m.binder_params
          in
          indent1 ^ "fn " ^ m.binder_value.name ^ params ^ " = "
          ^ fun_decl_ref_to_string env m.binder_value.item
          ^ "\n")
        (TraitMethodId.Map.values def.methods)
    in
    let vtable =
      match def.vtable with
      | Some vtb_ref ->
          [ indent1 ^ "vtable: " ^ type_decl_ref_to_string env vtb_ref ^ "\n" ]
      | None -> [ indent1 ^ "non-dyn-compatible\n" ]
    in
    let items = List.concat [ parent_clauses; consts; types; methods ] in
    if items = [] then "" else "\n{\n" ^ String.concat "" (items @ vtable) ^ "}"
  in

  intro ^ params ^ clauses ^ items

let trait_impl_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) (def : trait_impl) : string =
  let full_name = name_to_string env def.item_meta.name in
  let intro = indent ^ "// Full name: " ^ full_name ^ "\n" in
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr def.generics
  in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in

  let indent1 = indent ^ indent_incr in

  let items =
    let trait_id = def.impl_trait.id in
    (* The parent clauses are given by the trait refs of the implemented trait *)
    let parent_clauses =
      Collections.List.mapi
        (fun i trait_ref ->
          indent1 ^ "parent_clause" ^ string_of_int i ^ " = "
          ^ trait_ref_to_string env trait_ref
          ^ "\n")
        def.implied_trait_refs
    in
    let consts =
      List.map
        (fun (const_id, gref) ->
          let name =
            GAstUtils.get_assoc_const_name env.crate trait_id const_id
          in
          let gref = global_decl_ref_to_string env gref in
          indent1 ^ "const " ^ name ^ " = " ^ gref ^ "\n")
        (AssocConstId.Map.to_list def.consts)
    in
    let types =
      List.map
        (fun (type_id, bound_ty) ->
          let name = GAstUtils.get_assoc_type_name env.crate trait_id type_id in
          let env =
            fmt_env_push_generics_and_preds env bound_ty.binder_params
          in
          let params =
            generic_params_to_string_single_line env bound_ty.binder_params
          in
          indent1 ^ "type " ^ name ^ params ^ " = "
          ^ ty_to_string env bound_ty.binder_value.value
          ^ "\n")
        (AssocTypeId.Map.to_list def.types)
    in
    let methods =
      let trait_id = def.impl_trait.id in
      List.map
        (fun (method_id, (f : fun_decl_ref binder)) ->
          let name = GAstUtils.get_method_name env.crate trait_id method_id in
          let env = fmt_env_push_generics_and_preds env f.binder_params in
          let params =
            generic_params_to_string_single_line env f.binder_params
          in
          indent1 ^ "fn " ^ name ^ params ^ " = "
          ^ fun_decl_ref_to_string env f.binder_value
          ^ "\n")
        (TraitMethodId.Map.to_list def.methods)
    in
    let items = List.concat [ parent_clauses; consts; types; methods ] in
    let vtable =
      match def.vtable with
      | Some vtb_ref ->
          [
            indent1 ^ "vtable: " ^ global_decl_ref_to_string env vtb_ref ^ "\n";
          ]
      | None -> [ indent1 ^ "non-dyn-compatible\n" ]
    in
    let all_items = items @ vtable in
    if all_items = [] then " {}"
    else
      let open_brace = if clauses = "" then " {" else "\n{" in
      open_brace ^ "\n" ^ String.concat "" all_items ^ "}"
  in

  let impl_trait = trait_decl_ref_as_impl_to_string env def.impl_trait in
  intro ^ indent ^ "impl" ^ params ^ " " ^ impl_trait ^ clauses ^ items

let global_decl_to_string (env : fmt_env) (indent : string)
    (_indent_incr : string) (def : global_decl) : string =
  let keyword =
    match def.global_kind with
    | Static -> "static"
    | NamedConst | AnonConst -> "const"
  in
  let intro =
    item_intro_to_string env indent keyword (IdGlobal def.def_id) def.item_meta
  in
  (* Locally update the generics and the predicates *)
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent tab_incr def.generics
  in
  let params =
    if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
  in

  (* Type *)
  let ty = ty_to_string env def.ty in

  let body_id = fun_decl_id_to_string env def.init in
  intro ^ params ^ ": " ^ ty ^ clauses
  ^ (if clauses = "" then " " else "\n ")
  ^ "= " ^ body_id ^ "()"

module Llbc = struct
  (** Pretty-printing for LLBC AST (generic functions) *)

  open LlbcAst

  let rec statement_to_string (env : fmt_env) (indent : string)
      (indent_incr : string) (st : statement) : string =
    let comments =
      st.comments_before
      |> List.map (fun line -> indent ^ "// " ^ line ^ "\n")
      |> String.concat ""
    in
    comments ^ statement_kind_to_string env indent indent_incr st.kind

  and statement_kind_to_string (env : fmt_env) (indent : string)
      (indent_incr : string) (st : statement_kind) : string =
    match st with
    | Assign (p, rv) ->
        indent ^ place_to_string env p ^ " = " ^ rvalue_to_string env rv
    | SetDiscriminant (p, variant_id) ->
        indent ^ "@discriminant(" ^ place_to_string env p ^ ") = "
        ^ VariantId.to_string variant_id
    | CopyNonOverlapping { src; dst; count } ->
        indent ^ "copy_nonoverlapping(" ^ operand_to_string env src ^ ", "
        ^ operand_to_string env dst ^ ", "
        ^ operand_to_string env count
        ^ ")"
    | StorageLive var_id ->
        indent ^ "storage_live(" ^ local_id_to_string env var_id ^ ")"
    | StorageDead var_id ->
        indent ^ "storage_dead(" ^ local_id_to_string env var_id ^ ")"
    | PlaceMention place -> indent ^ "_ = " ^ place_to_string env place
    | Drop (p, fn_ptr, kind) ->
        let kind =
          match kind with
          | Precise -> "drop"
          | Conditional -> "conditional_drop"
        in
        indent ^ kind ^ "["
        ^ fn_ptr_to_string env fn_ptr
        ^ "] " ^ place_to_string env p
    | Assert (asrt, abort_kind) ->
        indent
        ^ assertion_to_string env asrt
        ^ " else "
        ^ abort_kind_to_string env abort_kind
    | Call call -> call_to_string env indent call
    | Abort kind -> indent ^ abort_kind_to_string env kind
    | Return -> indent ^ "return"
    | Break i -> indent ^ "break " ^ string_of_int i
    | Continue i -> indent ^ "continue " ^ string_of_int i
    | Nop -> indent ^ "nop"
    | Switch switch -> (
        match switch with
        | If (op, true_st, false_st) ->
            let op = operand_to_string env op in
            let inner_indent = indent ^ indent_incr in
            let inner_to_string =
              block_to_string env inner_indent indent_incr
            in
            let true_st = inner_to_string true_st in
            let false_st = inner_to_string false_st in
            indent ^ "if " ^ op ^ " {\n" ^ true_st ^ indent ^ "} else {\n"
            ^ false_st ^ indent ^ "}"
        | SwitchInt (op, _ty, branches, otherwise) ->
            let op = operand_to_string env op in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 = block_to_string env indent2 indent_incr in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    svl |> List.map literal_to_string |> String.concat " | "
                  in
                  indent1 ^ svl ^ " => {\n" ^ inner_to_string2 be ^ indent1
                  ^ "},")
                branches
            in
            let branches = String.concat "\n" branches in
            let branches =
              let sep = if branches = "" then "" else "\n" in
              branches ^ sep ^ indent1 ^ "_ => {\n" ^ inner_to_string2 otherwise
              ^ indent1 ^ "},"
            in
            indent ^ "switch " ^ op ^ " {\n" ^ branches ^ "\n" ^ indent ^ "}"
        | Match (place, branches, otherwise) ->
            let p = place_to_string env place in
            let discr_type =
              match place.ty with
              | TAdt { id = TAdtId type_id; _ } -> Some type_id
              | _ -> None
            in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 = block_to_string env indent2 indent_incr in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    List.map
                      (fun variant_id ->
                        match discr_type with
                        | Some type_id ->
                            adt_variant_to_string env type_id variant_id
                        | None -> variant_id_to_pretty_string variant_id)
                      svl
                  in
                  let svl = String.concat " | " svl in
                  indent1 ^ svl ^ " => {\n" ^ inner_to_string2 be ^ indent1
                  ^ "},")
                branches
            in
            let branches = String.concat "\n" branches in
            let otherwise =
              match otherwise with
              | None -> ""
              | Some otherwise ->
                  let sep = if branches = "" then "" else "\n" in
                  sep ^ indent1 ^ "_ => {\n" ^ inner_to_string2 otherwise
                  ^ indent1 ^ "},"
            in
            let branches = branches ^ otherwise in
            indent ^ "match " ^ p ^ " {\n" ^ branches ^ "\n" ^ indent ^ "}")
    | Loop loop_blk ->
        indent ^ "loop {\n"
        ^ block_to_string env (indent ^ indent_incr) indent_incr loop_blk
        ^ indent ^ "}"
    | Error s -> indent ^ "ERROR(' " ^ s ^ "')"

  and block_to_string (env : fmt_env) (indent : string) (indent_incr : string)
      (b : block) : string =
    let statements =
      List.map (statement_to_string env indent indent_incr) b.statements
    in
    if statements = [] then "" else String.concat "\n" statements ^ "\n"
end

module Ullbc = struct
  open UllbcAst

  let rec statement_to_string (env : fmt_env) (indent : string) (st : statement)
      : string =
    statement_kind_to_string env indent st.kind

  and statement_kind_to_string (env : fmt_env) (indent : string)
      (st : statement_kind) : string =
    match st with
    | Assign (p, rv) ->
        indent ^ place_to_string env p ^ " := " ^ rvalue_to_string env rv
    | SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id
           (we are missing the def id here) *)
        indent ^ "set_discriminant(" ^ place_to_string env p ^ ", "
        ^ variant_id_to_pretty_string variant_id
        ^ ")"
    | Assert (asrt, abort_kind) ->
        indent
        ^ assertion_to_string env asrt
        ^ " else "
        ^ abort_kind_to_string env abort_kind
    | StorageLive var_id ->
        indent ^ "storage_live " ^ local_id_to_string env var_id
    | StorageDead var_id ->
        indent ^ "storage_dead " ^ local_id_to_string env var_id
    | PlaceMention place -> indent ^ "_ := " ^ place_to_string env place
    | CopyNonOverlapping { src; dst; count } ->
        indent ^ "copy_non_overlapping(" ^ operand_to_string env src ^ ", "
        ^ operand_to_string env dst ^ ", "
        ^ operand_to_string env count
        ^ ")"
    | Nop -> "nop"

  let switch_to_string (indent : string) (tgt : switch) : string =
    match tgt with
    | If (b0, b1) ->
        let b0 = block_id_to_string b0 in
        let b1 = block_id_to_string b1 in
        indent ^ "[true -> " ^ b0 ^ "; false -> " ^ b1 ^ "]"
    | SwitchInt (_int_ty, branches, otherwise) ->
        let branches =
          List.map
            (fun (sv, bid) ->
              literal_to_string sv ^ " -> " ^ block_id_to_string bid ^ "; ")
            branches
        in
        let branches = String.concat "" branches in
        let otherwise = "_ -> " ^ block_id_to_string otherwise in
        indent ^ "[" ^ branches ^ otherwise ^ "]"

  let rec terminator_to_string (env : fmt_env) (indent : string)
      (st : terminator) : string =
    terminator_kind_to_string env indent st.kind

  and terminator_kind_to_string (env : fmt_env) (indent : string)
      (st : terminator_kind) : string =
    match st with
    | Goto bid -> indent ^ "goto " ^ block_id_to_string bid
    | Switch (op, tgts) ->
        indent ^ "switch " ^ operand_to_string env op
        ^ switch_to_string indent tgts
    | Call (call, tgt, unwind) ->
        call_to_string env indent call
        ^ " -> " ^ block_id_to_string tgt ^ "(unwind:"
        ^ block_id_to_string unwind ^ ")"
    | Drop (_, p, _, tgt, unwind) ->
        indent ^ "drop " ^ place_to_string env p ^ " -> "
        ^ block_id_to_string tgt ^ "(unwind:" ^ block_id_to_string unwind ^ ")"
    | TAssert (asrt, tgt, unwind) ->
        indent
        ^ assertion_to_string env asrt
        ^ " -> " ^ block_id_to_string tgt ^ "(unwind:"
        ^ block_id_to_string unwind ^ ")"
    | Abort _ -> indent ^ "panic"
    | Return -> indent ^ "return"
    | UnwindResume -> indent ^ "unwind_continue"

  let block_to_string (env : fmt_env) (indent : string) (indent_incr : string)
      (id : BlockId.id) (block : block) : string =
    let indent1 = indent ^ indent_incr in
    let statements =
      List.map
        (fun st -> statement_to_string env indent1 st ^ ";\n")
        block.statements
    in
    let terminator = terminator_to_string env indent1 block.terminator in
    indent ^ block_id_to_string id ^ " {\n"
    ^ String.concat "" statements
    ^ terminator ^ ";\n" ^ indent ^ "}"

  let blocks_to_string (env : fmt_env) (indent : string) (indent_incr : string)
      (blocks : block list) : string =
    let blocks = BlockId.mapi (block_to_string env indent indent_incr) blocks in
    String.concat "\n\n" blocks
end

let fun_decl_to_string (env : fmt_env) (indent : string) (indent_incr : string)
    (def : fun_decl) : string =
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
  let args =
    List.combine def.signature.inputs arg_names
    |> List.map (fun (ty, name) -> name ^ ": " ^ ty_to_string env ty)
    |> String.concat ", "
  in
  let ret_ty =
    if ty_is_unit def.signature.output then ""
    else " -> " ^ ty_to_string env def.signature.output
  in
  let header = intro ^ params ^ "(" ^ args ^ ")" ^ ret_ty ^ clauses in
  let body =
    match def.body with
    | StructuredBody { locals; body; _ } ->
        let env_locals = List.map (fun v -> (v.index, v.name)) locals.locals in
        let env = { env with locals = env_locals } in
        let body_indent = indent ^ indent_incr in
        "\n" ^ indent ^ "{\n"
        ^ locals_to_string env body_indent locals
        ^ "\n\n"
        ^ Llbc.block_to_string env body_indent indent_incr body
        ^ indent ^ "}"
    | UnstructuredBody { locals; body; _ } ->
        let env_locals = List.map (fun v -> (v.index, v.name)) locals.locals in
        let env = { env with locals = env_locals } in
        let body_indent = indent ^ indent_incr in
        "\n" ^ indent ^ "{\n"
        ^ locals_to_string env body_indent locals
        ^ "\n\n"
        ^ Ullbc.blocks_to_string env body_indent indent_incr body
        ^ "\n" ^ indent ^ "}"
    | TraitMethodWithoutDefaultBody ->
        "\n" ^ indent ^ "= <method_without_default_body>"
    | ExternBody name -> "\n" ^ indent ^ "= <extern:" ^ name ^ ">"
    | IntrinsicBody (name, _) -> "\n" ^ indent ^ "= <intrinsic:" ^ name ^ ">"
    | OpaqueBody -> "\n" ^ indent ^ "= <opaque>"
    | MissingBody -> "\n" ^ indent ^ "= <missing>"
    | ErrorBody error -> "\n" ^ indent ^ "= error(\"" ^ error.msg ^ "\")"
    | TargetDispatchBody targets ->
        let body_indent = indent ^ indent_incr in
        "\n" ^ indent ^ "= target_dispatch {\n"
        ^ String.concat ""
            (List.map
               (fun (target, fdecl) ->
                 body_indent ^ target ^ " => "
                 ^ fun_decl_ref_to_string env fdecl
                 ^ ",\n")
               targets)
        ^ indent ^ "}"
  in
  header ^ body

let crate_to_fmt_env (crate : crate) : fmt_env =
  { crate; generics = []; locals = [] }

let crate_to_string (m : crate) : string =
  let env : fmt_env = crate_to_fmt_env m in
  let format_item (id : item_id) : string =
    match id with
    | IdType id -> (
        match TypeDeclId.Map.find_opt id m.type_decls with
        | Some d -> type_decl_to_string env d
        | None -> "Missing decl: " ^ item_id_to_pretty_string (IdType id))
    | IdGlobal id -> (
        match GlobalDeclId.Map.find_opt id m.global_decls with
        | Some d -> global_decl_to_string env "" tab_incr d
        | None -> "Missing decl: " ^ item_id_to_pretty_string (IdGlobal id))
    | IdTraitDecl id -> (
        match TraitDeclId.Map.find_opt id m.trait_decls with
        | Some d -> trait_decl_to_string env "" tab_incr d
        | None -> "Missing decl: " ^ item_id_to_pretty_string (IdTraitDecl id))
    | IdTraitImpl id -> (
        match TraitImplId.Map.find_opt id m.trait_impls with
        | Some d -> trait_impl_to_string env "" tab_incr d
        | None -> "Missing decl: " ^ item_id_to_pretty_string (IdTraitImpl id))
    | IdFun id -> (
        match FunDeclId.Map.find_opt id m.fun_decls with
        | Some d -> fun_decl_to_string env "" tab_incr d
        | None -> "Missing decl: " ^ item_id_to_pretty_string (IdFun id))
  in
  let ids_of_group = function
    | NonRecGroup id -> [ id ]
    | RecGroup ids -> ids
  in
  let all_defs =
    if m.declarations = [] then
      let type_decls =
        List.map
          (fun (_, d) -> type_decl_to_string env d)
          (TypeDeclId.Map.bindings m.type_decls)
      in
      let global_decls =
        List.map
          (fun (_, d) -> global_decl_to_string env "" tab_incr d)
          (GlobalDeclId.Map.bindings m.global_decls)
      in
      let trait_decls =
        List.map
          (fun (_, d) -> trait_decl_to_string env "" tab_incr d)
          (TraitDeclId.Map.bindings m.trait_decls)
      in
      let trait_impls =
        List.map
          (fun (_, d) -> trait_impl_to_string env "" tab_incr d)
          (TraitImplId.Map.bindings m.trait_impls)
      in
      let fun_decls =
        List.map
          (fun (_, d) -> fun_decl_to_string env "" tab_incr d)
          (FunDeclId.Map.bindings m.fun_decls)
      in
      List.concat
        [ type_decls; global_decls; trait_decls; trait_impls; fun_decls ]
    else
      m.declarations
      |> List.concat_map (function
           | TypeGroup g -> List.map (fun id -> IdType id) (ids_of_group g)
           | FunGroup g -> List.map (fun id -> IdFun id) (ids_of_group g)
           | GlobalGroup g -> List.map (fun id -> IdGlobal id) (ids_of_group g)
           | TraitDeclGroup g ->
               List.map (fun id -> IdTraitDecl id) (ids_of_group g)
           | TraitImplGroup g ->
               List.map (fun id -> IdTraitImpl id) (ids_of_group g)
           | MixedGroup g -> ids_of_group g)
      |> List.map format_item
  in
  if all_defs = [] then "" else String.concat "\n\n" all_defs ^ "\n\n"
