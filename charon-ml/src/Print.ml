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
  ^ integer_type_to_string (Scalars.get_ty sv)

let float_value_to_string (fv : float_value) : string =
  fv.float_value ^ float_type_to_string fv.float_ty

let literal_to_string (lit : literal) : string =
  match lit with
  | VScalar sv -> scalar_value_to_string sv
  | VFloat fv -> float_value_to_string fv
  | VBool b -> Bool.to_string b
  | VChar c -> Uchar.to_string c
  | VStr s -> "\"" ^ s ^ "\""
  | VByteStr bs -> "[" ^ String.concat ", " (List.map string_of_int bs) ^ "]"

let region_param_to_string (rv : region_param) : string =
  match rv.name with
  | Some name -> name
  | None -> RegionId.to_string rv.index

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
  "T@" ^ de_bruijn_var_to_pretty_string TypeVarId.to_string var

let type_var_id_to_pretty_string (id : type_var_id) : string =
  "T@" ^ TypeVarId.to_string id

let type_param_to_string (tv : type_param) : string = tv.name

let const_generic_var_id_to_pretty_string (id : const_generic_var_id) : string =
  "C@" ^ ConstGenericVarId.to_string id

let const_generic_db_var_to_pretty_string (var : const_generic_db_var) : string
    =
  "C@" ^ de_bruijn_var_to_pretty_string ConstGenericVarId.to_string var

let const_generic_param_to_string (v : const_generic_param) : string = v.name

let trait_clause_id_to_pretty_string (id : trait_clause_id) : string =
  "TraitClause@" ^ TraitClauseId.to_string id

let trait_db_var_to_pretty_string (var : trait_db_var) : string =
  "TraitClause@" ^ de_bruijn_var_to_pretty_string TraitClauseId.to_string var

let trait_clause_id_to_string _ id = trait_clause_id_to_pretty_string id

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

let lookup_var_in_env (env : fmt_env)
    (find_in : generic_params -> 'id -> 'b option) (var : 'id de_bruijn_var) :
    'b option =
  if List.length env.generics == 0 then None
  else
    let dbid, varid =
      match var with
      | Bound (dbid, varid) -> (dbid, varid)
      | Free varid ->
          let len = List.length env.generics in
          let dbid = len - 1 in
          (dbid, varid)
    in
    match List.nth_opt env.generics dbid with
    | None -> None
    | Some generics -> begin
        match find_in generics varid with
        | None -> None
        | Some r -> Some r
      end

let region_db_var_to_string (env : fmt_env) (var : region_db_var) : string =
  (* Note that the regions are not necessarily ordered following their indices *)
  let find (generics : generic_params) varid =
    List.find_opt (fun (v : region_param) -> v.index = varid) generics.regions
  in
  match lookup_var_in_env env find var with
  | None -> region_db_var_to_pretty_string var
  | Some r -> region_param_to_string r

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
  | Some r -> const_generic_param_to_string r

let trait_db_var_to_string (env : fmt_env) (var : trait_db_var) : string =
  let find (generics : generic_params) varid =
    List.find_opt
      (fun (v : trait_param) -> v.clause_id = varid)
      generics.trait_clauses
  in
  match lookup_var_in_env env find var with
  | None -> trait_db_var_to_pretty_string var
  | Some r -> trait_clause_id_to_pretty_string r.clause_id

let region_to_string (env : fmt_env) (r : region) : string =
  match r with
  | RStatic -> "'static"
  | RErased -> "'_"
  | RBody id -> "°" ^ RegionId.to_string id
  | RVar var -> region_db_var_to_string env var

let region_binder_to_string (value_to_string : fmt_env -> 'c -> string)
    (env : fmt_env) (rb : 'c region_binder) : string =
  let env = fmt_env_push_regions env rb.binder_regions in
  let value = value_to_string env rb.binder_value in
  match rb.binder_regions with
  | [] -> value
  | _ ->
      "for <"
      ^ String.concat "," (List.map region_param_to_string rb.binder_regions)
      ^ "> " ^ value

let rec type_id_to_string (env : fmt_env) (id : type_id) : string =
  match id with
  | TAdtId id -> type_decl_id_to_string env id
  | TTuple -> ""
  | TBuiltin aty -> (
      match aty with
      | TBox -> "alloc::boxed::Box"
      | TStr -> "str")

and type_decl_id_to_string env def_id =
  (* We don't want the printing functions to crash if the crate is partial *)
  match TypeDeclId.Map.find_opt def_id env.crate.type_decls with
  | None -> type_decl_id_to_pretty_string def_id
  | Some def -> name_to_string env def.item_meta.name

and type_decl_ref_to_string (env : fmt_env) (tref : type_decl_ref) : string =
  match tref.id with
  | TTuple ->
      let params, trait_refs = generic_args_to_strings env tref.generics in
      "(" ^ String.concat ", " params ^ ")"
  | id ->
      let id = type_id_to_string env id in
      let generics = generic_args_to_string env tref.generics in
      id ^ generics

and fun_decl_id_to_string (env : fmt_env) (id : FunDeclId.id) : string =
  match FunDeclId.Map.find_opt id env.crate.fun_decls with
  | None -> fun_decl_id_to_pretty_string id
  | Some def -> name_to_string env def.item_meta.name

and fun_decl_ref_to_string (env : fmt_env) (fn : fun_decl_ref) : string =
  let fun_id = fun_decl_id_to_string env fn.id in
  let generics = generic_args_to_string env fn.generics in
  fun_id ^ generics

and global_decl_id_to_string env def_id =
  match GlobalDeclId.Map.find_opt def_id env.crate.global_decls with
  | None -> global_decl_id_to_pretty_string def_id
  | Some def -> name_to_string env def.item_meta.name

and global_decl_ref_to_string (env : fmt_env) (gr : global_decl_ref) : string =
  let global_id = global_decl_id_to_string env gr.id in
  let generics = generic_args_to_string env gr.generics in
  global_id ^ generics

and trait_decl_id_to_string env id =
  match TraitDeclId.Map.find_opt id env.crate.trait_decls with
  | None -> trait_decl_id_to_pretty_string id
  | Some def -> name_to_string env def.item_meta.name

and trait_impl_id_to_string env id =
  match TraitImplId.Map.find_opt id env.crate.trait_impls with
  | None -> trait_impl_id_to_pretty_string id
  | Some def -> name_to_string env def.item_meta.name

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
  | Uninit -> "uninit"
  | Value b -> string_of_int b
  | Provenance (p, i) ->
      provenance_to_string env p ^ "[" ^ string_of_int i ^ "]"

and const_aggregate_to_string (env : fmt_env) (tref : type_decl_ref)
    opt_variant_id (fields : constant_expr list) : string =
  let fields = List.map (constant_expr_to_string env) fields in

  match tref.id with
  | TTuple -> "(" ^ String.concat ", " fields ^ ")"
  | TAdtId def_id ->
      let adt_name = type_decl_id_to_string env def_id in
      let variant_name =
        match opt_variant_id with
        | None -> adt_name
        | Some variant_id ->
            adt_name ^ "::" ^ adt_variant_to_string env def_id variant_id
      in
      let fields =
        match adt_field_names env def_id opt_variant_id with
        | None -> "(" ^ String.concat ", " fields ^ ")"
        | Some field_names ->
            let fields = List.combine field_names fields in
            let fields =
              List.map
                (fun (field, value) -> field ^ " = " ^ value ^ ";")
                fields
            in
            let fields = String.concat " " fields in
            "{ " ^ fields ^ " }"
      in
      variant_name ^ " " ^ fields
  | TBuiltin _ -> raise (Failure "Unreachable")

and constant_expr_to_string (env : fmt_env) (cv : constant_expr) : string =
  match cv.kind with
  | CLiteral lit -> literal_to_string lit
  | CVar var -> const_generic_db_var_to_string env var
  | CTraitConst (trait_ref, const_name) ->
      let trait_ref = trait_ref_to_string env trait_ref in
      trait_ref ^ const_name
  | CVTableRef trait_ref ->
      let trait_ref = trait_ref_to_string env trait_ref in
      "&vtable_of(" ^ trait_ref ^ ")"
  | CFnDef fn_ptr | CFnPtr fn_ptr -> fn_ptr_to_string env fn_ptr
  | CRawMemory bytes ->
      "RawMemory(["
      ^ String.concat ", " (List.map (byte_to_string env) bytes)
      ^ "])"
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
  | CPtrNoProvenance n -> "(" ^ Z.to_string n ^ " as *const _)"
  | CRef (c, _) -> "&" ^ constant_expr_to_string env c
  | CPtr (ref_kind, c, _) ->
      let ref_kind =
        match ref_kind with
        | RShared -> "&raw const"
        | RMut -> "&raw mut"
      in
      ref_kind ^ constant_expr_to_string env c

and builtin_fun_id_to_string (aid : builtin_fun_id) : string =
  match aid with
  | BoxNew -> "alloc::boxed::Box::new"
  | ArrayToSliceShared -> "@ArrayToSliceShared"
  | ArrayToSliceMut -> "@ArrayToSliceMut"
  | ArrayRepeat -> "@ArrayRepeat"
  | Index { is_array; mutability; is_range } ->
      let ty = if is_array then "Array" else "Slice" in
      let op = if is_range then "SubSlice" else "Index" in
      let mutability = ref_kind_to_string mutability in
      "@" ^ ty ^ op ^ mutability
  | PtrFromParts mut ->
      let mut = if mut = RMut then "Mut" else "" in
      "@PtrFromParts" ^ mut

and fun_id_to_string (env : fmt_env) (fid : fun_id) : string =
  match fid with
  | FRegular fid -> fun_decl_id_to_string env fid
  | FBuiltin aid -> builtin_fun_id_to_string aid

and fn_ptr_kind_to_string (env : fmt_env) (r : fn_ptr_kind) : string =
  match r with
  | TraitMethod (trait_ref, method_name, _) ->
      trait_ref_to_string env trait_ref ^ "::" ^ method_name
  | FunId fid -> fun_id_to_string env fid

and fn_ptr_to_string (env : fmt_env) (ptr : fn_ptr) : string =
  let generics = generic_args_to_string env ptr.generics in
  fn_ptr_kind_to_string env ptr.kind ^ generics

and ty_to_string (env : fmt_env) (ty : ty) : string =
  match ty with
  | TAdt tref -> type_decl_ref_to_string env tref
  | TVar tv -> type_db_var_to_string env tv
  | TNever -> "!"
  | TLiteral lit_ty -> literal_type_to_string lit_ty
  | TTraitType (trait_ref, type_name) ->
      let trait_ref = trait_ref_to_string env trait_ref in
      trait_ref ^ "::" ^ type_name
  | TRef (r, rty, ref_kind) -> (
      match ref_kind with
      | RMut ->
          "&" ^ region_to_string env r ^ " mut (" ^ ty_to_string env rty ^ ")"
      | RShared ->
          "&" ^ region_to_string env r ^ " (" ^ ty_to_string env rty ^ ")")
  | TRawPtr (rty, ref_kind) -> (
      match ref_kind with
      | RMut -> "*mut " ^ ty_to_string env rty
      | RShared -> "*const " ^ ty_to_string env rty)
  | TFnPtr binder ->
      let env = fmt_env_push_regions env binder.binder_regions in
      let { inputs; output; _ } = binder.binder_value in
      let inputs =
        "(" ^ String.concat ", " (List.map (ty_to_string env) inputs) ^ ") -> "
      in
      inputs ^ ty_to_string env output
  | TFnDef f ->
      let env = fmt_env_push_regions env f.binder_regions in
      let fn = fn_ptr_to_string env f.binder_value in
      fn
  | TDynTrait pred ->
      let regions, clauses =
        generic_params_to_strings env pred.binder.binder_params
      in
      let reg_str =
        match regions with
        | [] -> ""
        | r :: _ -> " + " ^ r
      in
      "dyn (" ^ String.concat " + " clauses ^ reg_str ^ ")"
  | TArray (ty, len) ->
      "[" ^ ty_to_string env ty ^ "; " ^ constant_expr_to_string env len ^ "]"
  | TSlice ty -> "[" ^ ty_to_string env ty ^ "]"
  | TPtrMetadata ty -> "PtrMetadata(" ^ ty_to_string env ty ^ ")"
  | TError msg -> "type_error (\"" ^ msg ^ "\")"

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

and trait_ref_kind_to_string (env : fmt_env)
    (implements : trait_decl_ref region_binder option) (kind : trait_ref_kind) :
    string =
  match kind with
  | Self -> "Self"
  | TraitImpl impl_ref -> trait_impl_ref_to_string env impl_ref
  | BuiltinOrAuto _ ->
      region_binder_to_string trait_decl_ref_to_string env
        (Option.get implements)
  | Clause id -> trait_db_var_to_string env id
  | ParentClause (tref, clause_id) ->
      let inst_id = trait_ref_to_string env tref in
      let clause_id = trait_clause_id_to_string env clause_id in
      "parent(" ^ inst_id ^ ")::" ^ clause_id
  | ItemClause (tref, name, clause_id) ->
      let inst_id = trait_ref_to_string env tref in
      let clause_id = trait_clause_id_to_string env clause_id in
      "item(" ^ inst_id ^ ")::" ^ name ^ "::" ^ clause_id
  | Dyn ->
      let trait =
        region_binder_to_string trait_decl_ref_to_string env
          (Option.get implements)
      in
      "dyn(" ^ trait ^ ")"
  | UnknownTrait msg -> "UNKNOWN(" ^ msg ^ ")"

and trait_ref_to_string (env : fmt_env) (tr : trait_ref) : string =
  trait_ref_kind_to_string env (Some tr.trait_decl_ref) tr.kind

and trait_decl_ref_to_string (env : fmt_env) (tr : trait_decl_ref) : string =
  let trait_id = trait_decl_id_to_string env tr.id in
  let generics = generic_args_to_string env tr.generics in
  trait_id ^ generics

and impl_elem_to_string (env : fmt_env) (elem : impl_elem) : string =
  match elem with
  | ImplElemTy bound_ty ->
      (* Locally replace the generics and the predicates *)
      let env = fmt_env_push_generics_and_preds env bound_ty.binder_params in
      ty_to_string env bound_ty.binder_value
  | ImplElemTrait impl_id -> begin
      match TraitImplId.Map.find_opt impl_id env.crate.trait_impls with
      | None -> trait_impl_id_to_string env impl_id
      | Some impl -> (
          (* Locally replace the generics and the predicates *)
          let env = fmt_env_push_generics_and_preds env impl.generics in
          (* Put the first type argument aside (it gives the type for which we
             implement the trait) *)
          let { id; generics } : trait_decl_ref = impl.impl_trait in
          match generics.types with
          | ty :: types -> begin
              let ty, types = Collections.List.pop generics.types in
              let generics = { generics with types } in
              let tr : trait_decl_ref = { id; generics } in
              let ty = ty_to_string env ty in
              let tr = trait_decl_ref_to_string env tr in
              tr ^ " for " ^ ty
            end
          (* When monomorphizing, traits no longer take a `Self` argument, it's stored in the name *)
          | [] -> trait_decl_ref_to_string env impl.impl_trait)
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
      let env = fmt_env_push_generics_and_preds env binder.binder_params in
      let explicits, _ = generic_args_to_strings env binder.binder_value in
      "<" ^ String.concat ", " explicits ^ ">"
  | PeTarget target -> target

and name_to_string (env : fmt_env) (n : name) : string =
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
  let clause_id = trait_clause_id_to_string env clause.clause_id in
  let trait =
    region_binder_to_string trait_decl_ref_to_string env clause.trait
  in
  "[" ^ clause_id ^ "]: " ^ trait

and generic_params_to_strings (env : fmt_env) (generics : generic_params) :
    string list * string list =
  let ({ regions; types; const_generics; trait_clauses; _ } : generic_params) =
    generics
  in
  let regions = List.map region_param_to_string regions in
  let types = List.map type_param_to_string types in
  let cgs = List.map const_generic_param_to_string const_generics in
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
          name_to_string env def.item_meta.name ^ "::" ^ variant.variant_name
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
  | Some field_name -> field_name ^ " : " ^ ty_to_string env f.field_ty
  | None -> ty_to_string env f.field_ty

let variant_to_string env (v : variant) : string =
  v.variant_name ^ "("
  ^ String.concat ", " (List.map (field_to_string env) v.fields)
  ^ ")"

let trait_type_constraint_to_string (env : fmt_env)
    (ttc : trait_type_constraint) : string =
  let { trait_ref; type_name; ty } = ttc in
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
  let region_to_string = region_to_string env in
  let regions_outlive =
    let outlive_to_string _ (x, y) =
      region_to_string x ^ " : " ^ region_to_string y
    in
    List.map
      (region_binder_to_string outlive_to_string env)
      generics.regions_outlive
  in
  let types_outlive =
    let outlive_to_string _ (x, y) =
      ty_to_string env x ^ " : " ^ region_to_string y
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
           trait_clauses; regions_outlive; types_outlive; trait_type_constraints;
         ])
  in
  (params, clauses)

let type_decl_to_string (env : fmt_env) (def : type_decl) : string =
  (* Locally update the generics and the predicates *)
  let env = fmt_env_push_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env "" "  " def.generics
  in

  let name = name_to_string env def.item_meta.name in
  let params =
    if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
  in
  match def.kind with
  | Struct fields ->
      if fields <> [] then
        let fields =
          String.concat ""
            (List.map (fun f -> "\n  " ^ field_to_string env f ^ ",") fields)
        in
        "struct " ^ name ^ params ^ clauses ^ "\n{" ^ fields ^ "\n}"
      else "struct " ^ name ^ params ^ clauses ^ "{}"
  | Enum variants ->
      let variants =
        List.map (fun v -> "|  " ^ variant_to_string env v) variants
      in
      let variants = String.concat "\n" variants in
      "enum " ^ name ^ params ^ clauses ^ "\n  =\n" ^ variants
  | Union fields ->
      if fields <> [] then
        let fields =
          String.concat ""
            (List.map (fun f -> "\n  " ^ field_to_string env f ^ ",") fields)
        in
        "union " ^ name ^ params ^ clauses ^ "\n{" ^ fields ^ "\n}"
      else "union " ^ name ^ params ^ clauses ^ "{}"
  | Alias ty -> "type " ^ name ^ params ^ clauses ^ " = " ^ ty_to_string env ty
  | Opaque -> "opaque type " ^ name ^ params ^ clauses
  | TDeclError err -> "error(\"" ^ err ^ "\")"

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
  "v@" ^ LocalId.to_string id

let local_to_string (v : local) : string =
  match v.name with
  | None -> local_id_to_pretty_string v.index
  | Some name -> name ^ "^" ^ LocalId.to_string v.index

let local_id_to_string (env : fmt_env) (id : LocalId.id) : string =
  match List.find_opt (fun (i, _) -> i = id) env.locals with
  | None -> local_id_to_pretty_string id
  | Some (_, name) -> (
      match name with
      | None -> local_id_to_pretty_string id
      | Some name -> name ^ "^" ^ LocalId.to_string id)

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
  | Deref -> "*(" ^ sub ^ ")"
  | ProjIndex (off, from_end) ->
      let idx_pre = if from_end then "-" else "" in
      "(" ^ sub ^ ")[" ^ idx_pre ^ operand_to_string env off ^ "]"
  | Subslice (from, to_, from_end) ->
      let idx_pre = if from_end then "-" else "" in
      "(" ^ sub ^ ")[" ^ idx_pre ^ operand_to_string env from ^ ".."
      ^ operand_to_string env to_ ^ "]"
  | Field (ProjTuple _, fid) -> "(" ^ sub ^ ")." ^ FieldId.to_string fid
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
          "(" ^ sub ^ " as " ^ variant_name ^ ")." ^ field_name)
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
      "cast<" ^ literal_type_to_string src ^ "," ^ literal_type_to_string tgt
      ^ ">"
  | CastFnPtr (src, tgt) | CastRawPtr (src, tgt) | CastTransmute (src, tgt) ->
      "cast<" ^ ty_to_string env src ^ "," ^ ty_to_string env tgt ^ ">"
  | CastUnsize (src, tgt, _) ->
      "unsize<" ^ ty_to_string env src ^ "," ^ ty_to_string env tgt ^ ">"
  | CastConcretize (src, tgt) ->
      "concretize<" ^ ty_to_string env src ^ "," ^ ty_to_string env tgt ^ ">"

and nullop_to_string (env : fmt_env) (op : nullop) : string =
  match op with
  | SizeOf -> "size_of"
  | AlignOf -> "align_of"
  | OffsetOf _ -> "offset_of(?)"
  | UbChecks -> "ub_checks"
  | ContractChecks -> "contract_checks"
  | OverflowChecks -> "overflow_checks"

and unop_to_string (env : fmt_env) (unop : unop) : string =
  match unop with
  | Not -> "¬"
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
  | Constant cv -> constant_expr_to_string env cv

and aggregate_to_string (env : fmt_env) (agg : aggregate_kind)
    (fields : operand list) : string =
  let fields = List.map (operand_to_string env) fields in
  match agg with
  | AggregatedAdt (tref, opt_variant_id, opt_field_id) -> (
      match tref.id with
      | TTuple -> "(" ^ String.concat ", " fields ^ ")"
      | TAdtId def_id ->
          let adt_name = type_decl_id_to_string env def_id in
          let variant_name =
            match opt_variant_id with
            | None -> adt_name
            | Some variant_id ->
                adt_name ^ "::" ^ adt_variant_to_string env def_id variant_id
          in
          let fields =
            match adt_field_names env def_id opt_variant_id with
            | None -> "(" ^ String.concat ", " fields ^ ")"
            | Some field_names ->
                let field_names =
                  match opt_field_id with
                  | None -> field_names
                  (* Only keep the selected field *)
                  | Some field_id ->
                      [ List.nth field_names (FieldId.to_int field_id) ]
                in
                let fields = List.combine field_names fields in
                let fields =
                  List.map
                    (fun (field, value) -> field ^ " = " ^ value ^ ";")
                    fields
                in
                let fields = String.concat " " fields in
                "{ " ^ fields ^ " }"
          in
          variant_name ^ " " ^ fields
      | TBuiltin _ -> raise (Failure "Unreachable"))
  | AggregatedArray (_ty, _cg) -> "[" ^ String.concat ", " fields ^ "]"
  | AggregatedRawPtr (_, refk) ->
      let refk =
        match refk with
        | RShared -> "&raw const"
        | RMut -> "&raw mut"
      in
      refk ^ " (" ^ String.concat ", " fields ^ ")"

and rvalue_to_string (env : fmt_env) (rv : rvalue) : string =
  match rv with
  | Use op -> operand_to_string env op
  | RvRef (p, bk, op) -> begin
      let op = operand_to_string env op in
      let p = place_to_string env p in
      match bk with
      | BShared -> "&(" ^ p ^ ", " ^ op ^ ")"
      | BMut -> "&mut (" ^ p ^ ", " ^ op ^ ")"
      | BTwoPhaseMut -> "&two-phase (" ^ p ^ ", " ^ op ^ ")"
      | BUniqueImmutable -> "&uniq (" ^ p ^ ", " ^ op ^ ")"
      | BShallow -> "&shallow (" ^ p ^ ", " ^ op ^ ")"
    end
  | RawPtr (p, pk, op) -> begin
      let op = operand_to_string env op in
      let p = place_to_string env p in
      match pk with
      | RShared -> "&raw const (" ^ p ^ ", " ^ op ^ ")"
      | RMut -> "&raw mut (" ^ p ^ ", " ^ op ^ ")"
    end
  | NullaryOp (op, ty) ->
      nullop_to_string env op ^ "<" ^ ty_to_string env ty ^ ">"
  | UnaryOp (unop, op) ->
      unop_to_string env unop ^ " " ^ operand_to_string env op
  | BinaryOp (binop, op1, op2) ->
      operand_to_string env op1 ^ " " ^ binop_to_string binop ^ " "
      ^ operand_to_string env op2
  | Discriminant p -> "discriminant(" ^ place_to_string env p ^ ")"
  | Len (place, ty, const_generics) ->
      let const_generics =
        match const_generics with
        | None -> []
        | Some cg -> [ cg ]
      in
      "len<"
      ^ String.concat ", "
          (ty_to_string env ty
          :: List.map (constant_expr_to_string env) const_generics)
      ^ ">(" ^ place_to_string env place ^ ")"
  | Repeat (v, _, len) ->
      "[" ^ operand_to_string env v ^ ";"
      ^ constant_expr_to_string env len
      ^ "]"
  | ShallowInitBox (op, _) ->
      "shallow-init-box(" ^ operand_to_string env op ^ ")"
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
  indent ^ dest ^ " := move " ^ func ^ args

let assertion_to_string (env : fmt_env) (a : assertion) : string =
  let cond = operand_to_string env a.cond in
  if a.expected then "assert(" ^ cond ^ ")" else "assert(¬" ^ cond ^ ")"

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
         indent ^ local_to_string var ^ " : "
         ^ ty_to_string env var.local_ty
         ^ ";")
  |> String.concat "\n"

let trait_decl_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) (def : trait_decl) : string =
  (* Locally update the environment *)
  let env = fmt_env_replace_generics_and_preds env def.generics in

  let ty_to_string = ty_to_string env in

  (* Name *)
  let name = name_to_string env def.item_meta.name in

  (* Generics and predicates *)
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
          indent1 ^ "parent_clause_"
          ^ TraitClauseId.to_string clause.clause_id
          ^ " : "
          ^ trait_param_to_string env clause
          ^ "\n")
        def.implied_clauses
    in
    let consts =
      List.map
        (fun c ->
          let ty = ty_to_string c.ty in
          indent1 ^ "const " ^ c.name ^ " : " ^ ty ^ "\n")
        def.consts
    in
    let types =
      List.map
        (fun (bound_ty : trait_assoc_ty binder) ->
          let env =
            fmt_env_push_generics_and_preds env bound_ty.binder_params
          in
          (* TODO: print clauses too *)
          let params, _clauses =
            predicates_and_trait_clauses_to_string env "" "  " def.generics
          in
          let params =
            if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
          in
          indent1 ^ "type " ^ bound_ty.binder_value.name ^ params ^ "\n")
        def.types
    in
    let methods =
      List.map
        (fun (m : trait_method binder) ->
          indent1 ^ "fn " ^ m.binder_value.name ^ " : "
          ^ fun_decl_id_to_string env m.binder_value.item.id
          ^ "\n")
        def.methods
    in
    let items = List.concat [ parent_clauses; consts; types; methods ] in
    if items = [] then "" else "\n{\n" ^ String.concat "" items ^ "}"
  in

  "trait " ^ name ^ params ^ clauses ^ items

let trait_impl_to_string (env : fmt_env) (indent : string)
    (indent_incr : string) (def : trait_impl) : string =
  (* Locally update the environment *)
  let env = fmt_env_replace_generics_and_preds env def.generics in

  (* Name *)
  let name = name_to_string env def.item_meta.name in

  (* Generics and predicates *)
  let params, clauses =
    predicates_and_trait_clauses_to_string env indent indent_incr def.generics
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
        def.implied_trait_refs
    in
    let consts =
      List.map
        (fun (name, gref) ->
          let gref = global_decl_ref_to_string env gref in
          indent1 ^ "const " ^ name ^ " = " ^ gref ^ "\n")
        def.consts
    in
    let types =
      List.map
        (fun (name, bound_ty) ->
          let env =
            fmt_env_push_generics_and_preds env bound_ty.binder_params
          in
          let params, _clauses =
            predicates_and_trait_clauses_to_string env "" "  " def.generics
          in
          let params =
            if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
          in
          indent1 ^ "type " ^ name ^ params ^ " = "
          ^ ty_to_string env bound_ty.binder_value.value
          ^ "\n")
        def.types
    in
    let env_method ((name, f) : _ * fun_decl_ref binder) =
      indent1 ^ "fn " ^ name ^ " : "
      ^ fun_decl_id_to_string env f.binder_value.id
      ^ "\n"
    in
    let methods = List.map env_method def.methods in
    let items = List.concat [ parent_clauses; consts; types; methods ] in
    if items = [] then "" else "\n{\n" ^ String.concat "" items ^ "}"
  in

  let impl_trait = trait_decl_ref_to_string env def.impl_trait in
  "impl" ^ params ^ " " ^ name ^ params ^ " : " ^ impl_trait ^ clauses ^ items

let global_decl_to_string (env : fmt_env) (indent : string)
    (_indent_incr : string) (def : global_decl) : string =
  (* Locally update the generics and the predicates *)
  let env = fmt_env_replace_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env "" "  " def.generics
  in
  let params =
    if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
  in

  (* Global name *)
  let name = name_to_string env def.item_meta.name in

  (* Type *)
  let ty = ty_to_string env def.ty in

  let body_id = fun_decl_id_to_string env def.init in
  indent ^ "global " ^ name ^ params ^ clauses ^ " : " ^ ty ^ " = " ^ body_id

module Llbc = struct
  (** Pretty-printing for LLBC AST (generic functions) *)

  open LlbcAst

  let rec statement_to_string (env : fmt_env) (indent : string)
      (indent_incr : string) (st : statement) : string =
    statement_kind_to_string env indent indent_incr st.kind

  and statement_kind_to_string (env : fmt_env) (indent : string)
      (indent_incr : string) (st : statement_kind) : string =
    match st with
    | Assign (p, rv) ->
        indent ^ place_to_string env p ^ " := " ^ rvalue_to_string env rv
    | SetDiscriminant (p, variant_id) ->
        (* TODO: improve this to lookup the variant name by using the def id *)
        indent ^ "set_discriminant(" ^ place_to_string env p ^ ", "
        ^ VariantId.to_string variant_id
        ^ ")"
    | CopyNonOverlapping { src; dst; count } ->
        indent ^ "copy_non_overlapping(" ^ operand_to_string env src ^ ", "
        ^ operand_to_string env dst ^ ", "
        ^ operand_to_string env count
        ^ ")"
    | StorageLive var_id ->
        indent ^ "storage_live " ^ local_id_to_string env var_id
    | StorageDead var_id ->
        indent ^ "storage_dead " ^ local_id_to_string env var_id
    | PlaceMention place -> indent ^ "_ := " ^ place_to_string env place
    | Drop (p, _, _) -> indent ^ "drop " ^ place_to_string env p
    | Assert (asrt, abort_kind) ->
        indent
        ^ assertion_to_string env asrt
        ^ " else "
        ^ abort_kind_to_string env abort_kind
    | Call call -> call_to_string env indent call
    | Abort (Panic _) -> indent ^ "panic"
    | Abort UndefinedBehavior -> indent ^ "undefined_behavior"
    | Abort UnwindTerminate -> indent ^ "unwind_terminate"
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
            indent ^ "if (" ^ op ^ ") {\n" ^ true_st ^ "\n" ^ indent ^ "}\n"
            ^ indent ^ "else {\n" ^ false_st ^ "\n" ^ indent ^ "}"
        | SwitchInt (op, _ty, branches, otherwise) ->
            let op = operand_to_string env op in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 = block_to_string env indent2 indent_incr in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    List.map (fun sv -> "| " ^ literal_to_string sv) svl
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
        | Match (p, branches, otherwise) ->
            let p = place_to_string env p in
            let indent1 = indent ^ indent_incr in
            let indent2 = indent1 ^ indent_incr in
            let inner_to_string2 = block_to_string env indent2 indent_incr in
            let branches =
              List.map
                (fun (svl, be) ->
                  let svl =
                    List.map (fun sv -> "| " ^ VariantId.to_string sv) svl
                  in
                  let svl = String.concat " " svl in
                  indent ^ svl ^ " => {\n" ^ inner_to_string2 be ^ "\n"
                  ^ indent1 ^ "}")
                branches
            in
            let branches = String.concat "\n" branches in
            let otherwise =
              match otherwise with
              | None -> ""
              | Some otherwise ->
                  "\n" ^ indent1 ^ "_ => {\n" ^ inner_to_string2 otherwise
                  ^ "\n" ^ indent1 ^ "}"
            in
            let branches = branches ^ otherwise in
            indent ^ "match (" ^ p ^ ") {\n" ^ branches ^ "\n" ^ indent ^ "}")
    | Loop loop_blk ->
        indent ^ "loop {\n"
        ^ block_to_string env (indent ^ indent_incr) indent_incr loop_blk
        ^ "\n" ^ indent ^ "}"
    | Error s -> indent ^ "ERROR(' " ^ s ^ "')"

  and block_to_string (env : fmt_env) (indent : string) (indent_incr : string)
      (b : block) : string =
    String.concat ";\n"
      (List.map (statement_to_string env indent indent_incr) b.statements)
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
  (* Locally update the environment *)
  let env = fmt_env_replace_generics_and_preds env def.generics in

  let sg = def.signature in

  (* Function name *)
  let name = name_to_string env def.item_meta.name in

  (* We print the declaration differently if it is opaque (no body) or transparent
   * (we have access to a body) *)
  let sg = bound_fun_sig_of_decl def in
  match def.body with
  | Opaque
  | ErrorBody _
  | Missing
  | TraitMethodWithoutDefault
  | TargetDispatch _ ->
      let attrib =
        match def.body with
        | Opaque -> "opaque"
        | ErrorBody _ -> "error"
        | TraitMethodWithoutDefault -> "trait_method_without_default"
        | Missing -> "missing"
        | TargetDispatch targets ->
            "target_dispatch("
            ^ String.concat ", "
                (targets
                |> List.map (fun (target, fdecl) ->
                       target ^ " => " ^ fun_decl_ref_to_string env fdecl))
            ^ ")"
        | _ -> failwith "Impossible"
      in
      fun_sig_with_name_to_string env indent indent_incr (Some attrib)
        (Some name) None sg
  | Structured { locals; _ } | Unstructured { locals; _ } ->
      (* Locally update the environment *)
      let env_locals = List.map (fun v -> (v.index, v.name)) locals.locals in
      let env = { env with locals = env_locals } in

      (* Arguments *)
      let inputs = GAstUtils.locals_get_input_vars locals in

      (* All the locals (with erased regions) *)
      let locals = locals_to_string env (indent ^ indent_incr) locals in

      (* Body *)
      let body =
        match def.body with
        | Structured { body; _ } ->
            Llbc.block_to_string env (indent ^ indent_incr) indent_incr body
        | Unstructured { body; _ } ->
            Ullbc.blocks_to_string env (indent ^ indent_incr) indent_incr body
        | _ -> failwith "Impossible"
      in

      (* Put everything together *)
      fun_sig_with_name_to_string env indent indent_incr None (Some name)
        (Some inputs) sg
      ^ indent ^ "\n{\n" ^ locals ^ "\n\n" ^ body ^ "\n" ^ indent ^ "}"

let crate_to_fmt_env (crate : crate) : fmt_env =
  { crate; generics = []; locals = [] }

let crate_to_string (m : crate) : string =
  let env : fmt_env = crate_to_fmt_env m in

  (* The types *)
  let type_decls =
    List.map
      (fun (_, d) -> type_decl_to_string env d)
      (TypeDeclId.Map.bindings m.type_decls)
  in

  (* The globals *)
  let global_decls =
    List.map
      (fun (_, d) -> global_decl_to_string env "" "  " d)
      (GlobalDeclId.Map.bindings m.global_decls)
  in

  (* The functions *)
  let fun_decls =
    List.map
      (fun (_, d) -> fun_decl_to_string env "" "  " d)
      (FunDeclId.Map.bindings m.fun_decls)
  in

  (* The trait declarations *)
  let trait_decls =
    List.map
      (fun (_, d) -> trait_decl_to_string env "" "  " d)
      (TraitDeclId.Map.bindings m.trait_decls)
  in

  (* The trait implementations *)
  let trait_impls =
    List.map
      (fun (_, d) -> trait_impl_to_string env "" "  " d)
      (TraitImplId.Map.bindings m.trait_impls)
  in

  (* Put everything together *)
  let all_defs =
    List.concat
      [ type_decls; global_decls; trait_decls; trait_impls; fun_decls ]
  in
  String.concat "\n\n" all_defs
