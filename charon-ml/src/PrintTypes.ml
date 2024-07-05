(** Pretty-printing for types *)

include PrintValues
open Types
open TypesUtils
open GAst
open PrintUtils

let type_var_to_string (tv : type_var) : string = tv.name
let const_generic_var_to_string (v : const_generic_var) : string = v.name

let region_var_to_string (rv : region_var) : string =
  match rv.name with
  | Some name -> name
  | None -> RegionVarId.to_string rv.index

let ref_kind_to_string (rk : ref_kind) : string =
  match rk with RMut -> "Mut" | RShared -> "Shared"

let assumed_ty_to_string (_ : assumed_ty) : string = "Box"

let trait_clause_id_to_pretty_string (id : trait_clause_id) : string =
  "TraitClause@" ^ TraitClauseId.to_string id

let region_var_id_to_pretty_string (db_id : region_db_id) (id : region_var_id) :
    string =
  "'" ^ show_region_db_id db_id ^ "_" ^ RegionVarId.to_string id

let region_id_to_pretty_string (id : region_id) : string =
  "'" ^ RegionId.to_string id

let type_var_id_to_pretty_string (id : type_var_id) : string =
  "T@" ^ TypeVarId.to_string id

let const_generic_var_id_to_pretty_string (id : const_generic_var_id) : string =
  "C@" ^ ConstGenericVarId.to_string id

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

let region_var_id_to_string (env : ('a, 'b) fmt_env) (db_id : region_db_id)
    (id : region_var_id) : string =
  match List.nth_opt env.regions db_id with
  | None -> region_var_id_to_pretty_string db_id id
  | Some regions -> (
      (* Note that the regions are not necessarily ordered following their indices *)
      match List.find_opt (fun (r : region_var) -> r.index = id) regions with
      | None -> region_var_id_to_pretty_string db_id id
      | Some r -> region_var_to_string r)

let type_var_id_to_string (env : ('a, 'b) fmt_env) (id : type_var_id) : string =
  (* Note that the types are not necessarily ordered following their indices *)
  match
    List.find_opt (fun (x : type_var) -> x.index = id) env.generics.types
  with
  | None -> type_var_id_to_pretty_string id
  | Some x -> type_var_to_string x

let const_generic_var_id_to_string (env : ('a, 'b) fmt_env)
    (id : const_generic_var_id) : string =
  (* Note that the const generics are not necessarily ordered following their indices *)
  match
    List.find_opt
      (fun (x : const_generic_var) -> x.index = id)
      env.generics.const_generics
  with
  | None -> const_generic_var_id_to_pretty_string id
  | Some x -> const_generic_var_to_string x

let region_to_string (env : ('a, 'b) fmt_env) (r : region) : string =
  match r with
  | RStatic -> "'static"
  | RErased -> "'_"
  | RBVar (db, rid) -> region_var_id_to_string env db rid
  | RFVar rid -> region_id_to_pretty_string rid

let trait_clause_id_to_string _ id = trait_clause_id_to_pretty_string id

let rec type_id_to_string (env : ('a, 'b) fmt_env) (id : type_id) : string =
  match id with
  | TAdtId id -> type_decl_id_to_string env id
  | TTuple -> ""
  | TAssumed aty -> (
      match aty with
      | TBox -> "alloc::boxed::Box"
      | TStr -> "str"
      | TArray -> "@Array"
      | TSlice -> "@Slice")

and type_decl_id_to_string env def_id =
  (* We don't want the printing functions to crash if the crate is partial *)
  match TypeDeclId.Map.find_opt def_id env.type_decls with
  | None -> type_decl_id_to_pretty_string def_id
  | Some def -> name_to_string env def.item_meta.name

and fun_decl_id_to_string (env : ('a, 'b) fmt_env) (id : FunDeclId.id) : string
    =
  match FunDeclId.Map.find_opt id env.fun_decls with
  | None -> fun_decl_id_to_pretty_string id
  | Some def -> name_to_string env def.item_meta.name

and global_decl_id_to_string env def_id =
  match GlobalDeclId.Map.find_opt def_id env.global_decls with
  | None -> global_decl_id_to_pretty_string def_id
  | Some def -> name_to_string env def.item_meta.name

and trait_decl_id_to_string env id =
  match TraitDeclId.Map.find_opt id env.trait_decls with
  | None -> trait_decl_id_to_pretty_string id
  | Some def -> name_to_string env def.item_meta.name

and trait_impl_id_to_string env id =
  match TraitImplId.Map.find_opt id env.trait_impls with
  | None -> trait_impl_id_to_pretty_string id
  | Some def -> name_to_string env def.item_meta.name

and const_generic_to_string (env : ('a, 'b) fmt_env) (cg : const_generic) :
    string =
  match cg with
  | CgGlobal id -> global_decl_id_to_string env id
  | CgVar id -> const_generic_var_id_to_string env id
  | CgValue lit -> literal_to_string lit

and ty_to_string (env : ('a, 'b) fmt_env) (ty : ty) : string =
  match ty with
  | TAdt (id, generics) ->
      let is_tuple = match id with TTuple -> true | _ -> false in
      let params = params_to_string env is_tuple generics in
      type_id_to_string env id ^ params
  | TVar tv -> type_var_id_to_string env tv
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
  | TArrow (regions, inputs, output) ->
      let env = { env with regions = regions :: env.regions } in
      let inputs =
        "(" ^ String.concat ", " (List.map (ty_to_string env) inputs) ^ ") -> "
      in
      inputs ^ ty_to_string env output
  | TDynTrait _ -> "dyn (TODO)"

and params_to_string (env : ('a, 'b) fmt_env) (is_tuple : bool)
    (generics : generic_args) : string =
  if is_tuple then
    (* Remark: there shouldn't be any trait ref, but we still print them
       because if there are we *want* to see them (for debugging purposes) *)
    let params, trait_refs = generic_args_to_strings env generics in
    let params = "(" ^ String.concat ", " params ^ ")" in
    let trait_refs =
      if trait_refs = [] then "" else "[" ^ String.concat ", " trait_refs ^ "]"
    in
    params ^ trait_refs
  else generic_args_to_string env generics

(** Return two lists:
    - one for the regions, types, const generics
    - one for the trait refs
 *)
and generic_args_to_strings (env : ('a, 'b) fmt_env) (generics : generic_args) :
    string list * string list =
  let { regions; types; const_generics; trait_refs } = generics in
  let regions = List.map (region_to_string env) regions in
  let types = List.map (ty_to_string env) types in
  let cgs = List.map (const_generic_to_string env) const_generics in
  let params = List.flatten [ regions; types; cgs ] in
  let trait_refs = List.map (trait_ref_to_string env) trait_refs in
  (params, trait_refs)

and generic_args_to_string (env : ('a, 'b) fmt_env) (generics : generic_args) :
    string =
  let params, trait_refs = generic_args_to_strings env generics in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in
  let trait_refs =
    if trait_refs = [] then "" else "[" ^ String.concat ", " trait_refs ^ "]"
  in
  params ^ trait_refs

and trait_ref_to_string (env : ('a, 'b) fmt_env) (tr : trait_ref) : string =
  trait_instance_id_to_string env tr.trait_id

and trait_decl_ref_to_string (env : ('a, 'b) fmt_env) (tr : trait_decl_ref) :
    string =
  let trait_id = trait_decl_id_to_string env tr.trait_decl_id in
  let generics = generic_args_to_string env tr.decl_generics in
  trait_id ^ generics

and trait_instance_id_to_string (env : ('a, 'b) fmt_env)
    (id : trait_instance_id) : string =
  match id with
  | Self -> "Self"
  | TraitImpl (id, generics) ->
      let impl = trait_impl_id_to_string env id in
      let generics = generic_args_to_string env generics in
      impl ^ generics
  | BuiltinOrAuto trait -> trait_decl_ref_to_string env trait
  | Clause id -> trait_clause_id_to_string env id
  | ParentClause (inst_id, _decl_id, clause_id) ->
      let inst_id = trait_instance_id_to_string env inst_id in
      let clause_id = trait_clause_id_to_string env clause_id in
      "parent(" ^ inst_id ^ ")::" ^ clause_id
  | ItemClause (inst_id, _decl_id, item_name, clause_id) ->
      let inst_id = trait_instance_id_to_string env inst_id in
      let clause_id = trait_clause_id_to_string env clause_id in
      "(" ^ inst_id ^ ")::" ^ item_name ^ "::[" ^ clause_id ^ "]"
  | TraitRef tr -> trait_ref_to_string env tr
  | FnPointer ty -> "fn_ptr(" ^ ty_to_string env ty ^ ")"
  | Closure (fid, generics) ->
      "closure("
      ^ fun_decl_id_to_string env fid
      ^ generic_args_to_string env generics
      ^ ")"
  | Dyn trait ->
      let trait = trait_decl_ref_to_string env trait in
      "dyn(" ^ trait ^ ")"
  | Unsolved (decl_id, generics) ->
      "unsolved("
      ^ trait_decl_id_to_string env decl_id
      ^ generic_args_to_string env generics
      ^ ")"
  | UnknownTrait msg -> "UNKNOWN(" ^ msg ^ ")"

and impl_elem_kind_to_string (env : ('a, 'b) fmt_env) (k : impl_elem_kind) :
    string =
  match k with
  | ImplElemTy ty -> ty_to_string env ty
  | ImplElemTrait tr ->
      (* Put the first type argument aside (it gives the type for which we
         implement the trait) *)
      let { trait_decl_id; decl_generics } = tr in
      let ty, types = Collections.List.pop decl_generics.types in
      let decl_generics = { decl_generics with types } in
      let ty = ty_to_string env ty in
      let tr = { trait_decl_id; decl_generics } in
      let tr = trait_decl_ref_to_string env tr in
      "(" ^ tr ^ " for " ^ ty ^ ")"

and impl_elem_to_string (env : ('a, 'b) fmt_env) (e : impl_elem) : string =
  (* Locally replace the generics and the predicates *)
  let env = fmt_env_update_generics_and_preds env e.generics in
  let d =
    if e.disambiguator = Disambiguator.zero then ""
    else "#" ^ Disambiguator.to_string e.disambiguator
  in
  let kind = impl_elem_kind_to_string env e.kind in
  "{" ^ kind ^ d ^ "}"

and path_elem_to_string (env : ('a, 'b) fmt_env) (e : path_elem) : string =
  match e with
  | PeIdent (s, d) ->
      let d =
        if d = Disambiguator.zero then "" else "#" ^ Disambiguator.to_string d
      in
      s ^ d
  | PeImpl impl -> impl_elem_to_string env impl

and name_to_string (env : ('a, 'b) fmt_env) (n : name) : string =
  let name = List.map (path_elem_to_string env) n in
  String.concat "::" name

let trait_clause_to_string (env : ('a, 'b) fmt_env) (clause : trait_clause) :
    string =
  let clause_id = trait_clause_id_to_string env clause.clause_id in
  let trait = trait_decl_ref_to_string env clause.trait in
  "[" ^ clause_id ^ "]: " ^ trait

let generic_params_to_strings (env : ('a, 'b) fmt_env)
    (generics : generic_params) : string list * string list =
  let { regions; types; const_generics; trait_clauses; _ } : generic_params =
    generics
  in
  let regions = List.map region_var_to_string regions in
  let types = List.map type_var_to_string types in
  let cgs = List.map const_generic_var_to_string const_generics in
  let params = List.flatten [ regions; types; cgs ] in
  let trait_clauses = List.map (trait_clause_to_string env) trait_clauses in
  (params, trait_clauses)

let field_to_string env (f : field) : string =
  match f.field_name with
  | Some field_name -> field_name ^ " : " ^ ty_to_string env f.field_ty
  | None -> ty_to_string env f.field_ty

let variant_to_string env (v : variant) : string =
  v.variant_name ^ "("
  ^ String.concat ", " (List.map (field_to_string env) v.fields)
  ^ ")"

let trait_type_constraint_to_string (env : ('a, 'b) fmt_env)
    (ttc : trait_type_constraint) : string =
  let { trait_ref; type_name; ty } = ttc in
  let trait_ref = trait_ref_to_string env trait_ref in
  let ty = ty_to_string env ty in
  trait_ref ^ "::" ^ type_name ^ " = " ^ ty

(** Helper to format "where" clauses *)
let clauses_to_string (indent : string) (indent_incr : string)
    (num_inherited_clauses : int) (clauses : string list) : string =
  if clauses = [] then ""
  else
    let env_clause s = indent ^ indent_incr ^ s ^ "," in
    let clauses = List.map env_clause clauses in
    let inherited, local =
      Collections.List.split_at clauses num_inherited_clauses
    in
    let delim1 =
      if inherited <> [] then [ indent ^ "  // Inherited clauses" ] else []
    in
    let delim2 =
      if inherited <> [] && local <> [] then [ indent ^ "  // Local clauses" ]
      else []
    in
    let clauses =
      List.concat [ [ indent ^ "where" ]; delim1; inherited; delim2; local ]
    in
    "\n" ^ String.concat "\n" clauses

(** Helper to format "where" clauses *)
let predicates_and_trait_clauses_to_string (env : ('a, 'b) fmt_env)
    (indent : string) (indent_incr : string) (params_info : params_info option)
    (generics : generic_params) : string list * string =
  let params, trait_clauses = generic_params_to_strings env generics in
  let region_to_string = region_to_string env in
  let regions_outlive =
    List.map
      (fun (x, y) -> region_to_string x ^ " : " ^ region_to_string y)
      generics.regions_outlive
  in
  let types_outlive =
    List.map
      (fun (x, y) -> ty_to_string env x ^ " : " ^ region_to_string y)
      generics.types_outlive
  in
  let trait_type_constraints =
    List.map
      (trait_type_constraint_to_string env)
      generics.trait_type_constraints
  in
  (* Split between the inherited clauses and the local clauses *)
  let clauses =
    match params_info with
    | None ->
        let clauses =
          List.concat [ regions_outlive; types_outlive; trait_type_constraints ]
        in
        clauses_to_string indent indent_incr 0 clauses
    | Some pi ->
        let split_at = Collections.List.split_at in
        let trait_clauses = split_at trait_clauses pi.num_trait_clauses in
        let regions_outlive = split_at regions_outlive pi.num_regions_outlive in
        let types_outlive = split_at types_outlive pi.num_types_outlive in
        let ttc =
          split_at trait_type_constraints pi.num_trait_type_constraints
        in
        let inherited, local =
          List.split [ trait_clauses; regions_outlive; types_outlive; ttc ]
        in
        let inherited = List.concat inherited in
        let local = List.concat local in
        let num_inherited = List.length inherited in
        let clauses = List.append inherited local in
        clauses_to_string indent indent_incr num_inherited clauses
  in
  (params, clauses)

let type_decl_to_string (env : ('a, 'b) fmt_env) (def : type_decl) : string =
  (* Locally update the generics and the predicates *)
  let env = fmt_env_update_generics_and_preds env def.generics in
  let params, clauses =
    predicates_and_trait_clauses_to_string env "" "  " None def.generics
  in

  let name = name_to_string env def.item_meta.name in
  let params =
    if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
  in
  match def.kind with
  | Struct fields ->
      if fields <> [] then
        let fields =
          String.concat ","
            (List.map (fun f -> "\n  " ^ field_to_string env f) fields)
        in
        "struct " ^ name ^ params ^ clauses ^ "\n{" ^ fields ^ "\n}"
      else "struct " ^ name ^ params ^ clauses ^ "{}"
  | Enum variants ->
      let variants =
        List.map (fun v -> "|  " ^ variant_to_string env v) variants
      in
      let variants = String.concat "\n" variants in
      "enum " ^ name ^ params ^ clauses ^ "\n  =\n" ^ variants
  | Alias ty -> "type " ^ name ^ params ^ clauses ^ " = " ^ ty_to_string env ty
  | Opaque -> "opaque type " ^ name ^ params ^ clauses

let adt_variant_to_string (env : ('a, 'b) fmt_env) (def_id : TypeDeclId.id)
    (variant_id : VariantId.id) : string =
  match TypeDeclId.Map.find_opt def_id env.type_decls with
  | None ->
      type_decl_id_to_pretty_string def_id
      ^ "::"
      ^ variant_id_to_pretty_string variant_id
  | Some def -> (
      match def.kind with
      | Struct _ | Alias _ | Opaque -> raise (Failure "Unreachable")
      | Enum variants ->
          let variant = VariantId.nth variants variant_id in
          name_to_string env def.item_meta.name ^ "::" ^ variant.variant_name)

let adt_field_names (env : ('a, 'b) fmt_env) (def_id : TypeDeclId.id)
    (opt_variant_id : VariantId.id option) : string list option =
  match TypeDeclId.Map.find_opt def_id env.type_decls with
  | None -> None
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

let adt_field_to_string (env : ('a, 'b) fmt_env) (def_id : TypeDeclId.id)
    (opt_variant_id : VariantId.id option) (field_id : FieldId.id) :
    string option =
  match TypeDeclId.Map.find_opt def_id env.type_decls with
  | None -> None
  | Some def ->
      let fields = type_decl_get_fields def opt_variant_id in
      let field = FieldId.nth fields field_id in
      field.field_name
