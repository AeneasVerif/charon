(** Pretty-printing for types *)

module T = Types
module TU = TypesUtils
module E = Expressions
module A = LlbcAst
module PV = PrimitiveValues
open PrintUtils
open PrintPrimitiveValues

let type_var_id_to_string (id : T.TypeVarId.id) : string =
  "T@" ^ T.TypeVarId.to_string id

let type_var_to_string (tv : T.type_var) : string = tv.name

let const_generic_var_id_to_string (id : T.ConstGenericVarId.id) : string =
  "N@" ^ T.ConstGenericVarId.to_string id

let const_generic_var_to_string (v : T.const_generic_var) : string = v.name

let region_var_to_string (rv : T.region_var) : string =
  match rv.name with
  | Some name -> name
  | None -> T.RegionVarId.to_string rv.index

let region_var_id_to_string (rid : T.RegionVarId.id) : string =
  "rv@" ^ T.RegionVarId.to_string rid

let region_id_to_string (rid : T.RegionId.id) : string =
  "r@" ^ T.RegionId.to_string rid

let region_to_string (rid_to_string : 'rid -> string) (r : 'rid T.region) :
    string =
  match r with Static -> "'static" | Var rid -> rid_to_string rid

let erased_region_to_string (_ : T.erased_region) : string = "'_"

let ref_kind_to_string (rk : T.ref_kind) : string =
  match rk with Mut -> "Mut" | Shared -> "Shared"

let assumed_ty_to_string (_ : T.assumed_ty) : string = "Box"

let trait_clause_id_to_pretty_string (id : T.trait_clause_id) : string =
  "@TraitClause" ^ T.TraitClauseId.to_string id

type 'r type_formatter = {
  r_to_string : 'r -> string;
  type_var_id_to_string : T.TypeVarId.id -> string;
  type_decl_id_to_string : T.TypeDeclId.id -> string;
  const_generic_var_id_to_string : T.ConstGenericVarId.id -> string;
  global_decl_id_to_string : T.GlobalDeclId.id -> string;
  trait_decl_id_to_string : T.TraitDeclId.id -> string;
  trait_impl_id_to_string : T.TraitImplId.id -> string;
  trait_clause_id_to_string : T.TraitClauseId.id -> string;
}

type stype_formatter = T.RegionVarId.id T.region type_formatter
type rtype_formatter = T.RegionId.id T.region type_formatter
type etype_formatter = T.erased_region type_formatter

let type_id_to_string (fmt : 'r type_formatter) (id : T.type_id) : string =
  match id with
  | T.AdtId id -> fmt.type_decl_id_to_string id
  | T.Tuple -> ""
  | T.Assumed aty -> (
      match aty with
      | Box -> "alloc::boxed::Box"
      | Vec -> "alloc::vec::Vec"
      | Option -> "core::option::Option"
      | Str -> "str"
      | Array -> "@Array"
      | Slice -> "@Slice"
      | Range -> "@Range")

let const_generic_to_string (fmt : 'r type_formatter) (cg : T.const_generic) :
    string =
  match cg with
  | ConstGenericGlobal id -> fmt.global_decl_id_to_string id
  | ConstGenericVar id -> fmt.const_generic_var_id_to_string id
  | ConstGenericValue lit -> literal_to_string lit

let rec ty_to_string (fmt : 'r type_formatter) (ty : 'r T.ty) : string =
  match ty with
  | T.Adt (id, generics) ->
      let is_tuple = match id with T.Tuple -> true | _ -> false in
      let params = params_to_string fmt is_tuple generics in
      type_id_to_string fmt id ^ params
  | T.TypeVar tv -> fmt.type_var_id_to_string tv
  | T.Never -> "!"
  | T.Literal lit_ty -> literal_type_to_string lit_ty
  | T.TraitType (trait_ref, generics, type_name) ->
      let trait_ref = trait_ref_to_string fmt trait_ref in
      let generics = generic_args_to_string fmt generics in
      trait_ref ^ generics ^ "::" ^ type_name
  | T.Ref (r, rty, ref_kind) -> (
      match ref_kind with
      | T.Mut -> "&" ^ fmt.r_to_string r ^ " mut (" ^ ty_to_string fmt rty ^ ")"
      | T.Shared -> "&" ^ fmt.r_to_string r ^ " (" ^ ty_to_string fmt rty ^ ")")

and params_to_string (fmt : 'r type_formatter) (is_tuple : bool)
    (generics : 'r T.generic_args) : string =
  if is_tuple then
    (* Remark: there shouldn't be any trait ref, but we still print them
       because if there are we *want* to see them (for debugging purposes) *)
    let params, trait_refs = generic_args_to_strings fmt generics in
    let params = "(" ^ String.concat ", " params ^ ")" in
    let trait_refs =
      if trait_refs = [] then "" else "[" ^ String.concat ", " trait_refs ^ "]"
    in
    params ^ trait_refs
  else generic_args_to_string fmt generics

(** Return two lists:
    - one for the regions, types, const generics
    - one for the trait refs
 *)
and generic_args_to_strings (fmt : 'r type_formatter)
    (generics : 'r T.generic_args) : string list * string list =
  let { T.regions; types; const_generics; trait_refs } = generics in
  let regions = List.map fmt.r_to_string regions in
  let types = List.map (ty_to_string fmt) types in
  let cgs = List.map (const_generic_to_string fmt) const_generics in
  let params = List.flatten [ regions; types; cgs ] in
  let trait_refs = List.map (trait_ref_to_string fmt) trait_refs in
  (params, trait_refs)

and generic_args_to_string (fmt : 'r type_formatter)
    (generics : 'r T.generic_args) : string =
  let params, trait_refs = generic_args_to_strings fmt generics in
  let params =
    if params = [] then "" else "<" ^ String.concat ", " params ^ ">"
  in
  let trait_refs =
    if trait_refs = [] then "" else "[" ^ String.concat ", " trait_refs ^ "]"
  in
  params ^ trait_refs

and trait_ref_to_string (fmt : 'r type_formatter) (tr : 'r T.trait_ref) : string
    =
  let trait_id = trait_instance_id_to_string fmt tr.T.trait_id in
  let generics = generic_args_to_string fmt tr.T.generics in
  trait_id ^ generics

and trait_decl_ref_to_string (fmt : 'r type_formatter)
    (tr : 'r T.trait_decl_ref) : string =
  let trait_id = fmt.trait_decl_id_to_string tr.T.trait_decl_id in
  let generics = generic_args_to_string fmt tr.T.decl_generics in
  trait_id ^ generics

and trait_instance_id_to_string (fmt : 'r type_formatter)
    (id : 'r T.trait_instance_id) : string =
  match id with
  | Self -> "Self"
  | TraitImpl id -> fmt.trait_impl_id_to_string id
  | BuiltinOrAuto id -> fmt.trait_decl_id_to_string id
  | Clause id -> fmt.trait_clause_id_to_string id
  | ParentClause (inst_id, _decl_id, clause_id) ->
      let inst_id = trait_instance_id_to_string fmt inst_id in
      let clause_id = fmt.trait_clause_id_to_string clause_id in
      "parent(" ^ inst_id ^ ")::" ^ clause_id
  | ItemClause (inst_id, _decl_id, item_name, clause_id) ->
      let inst_id = trait_instance_id_to_string fmt inst_id in
      let clause_id = fmt.trait_clause_id_to_string clause_id in
      "(" ^ inst_id ^ ")::" ^ item_name ^ "::[" ^ clause_id ^ "]"
  | TraitRef tr -> trait_ref_to_string fmt tr
  | UnknownTrait msg -> "UNKNOWN(" ^ msg ^ ")"

let sty_to_string (fmt : stype_formatter) (ty : T.sty) : string =
  ty_to_string fmt ty

let rty_to_string (fmt : rtype_formatter) (ty : T.rty) : string =
  ty_to_string fmt ty

let ety_to_string (fmt : etype_formatter) (ty : T.ety) : string =
  ty_to_string fmt ty

let strait_ref_to_string (fmt : stype_formatter) (trait_ref : T.strait_ref) :
    string =
  trait_ref_to_string fmt trait_ref

let rtrait_ref_to_string (fmt : rtype_formatter) (trait_ref : T.rtrait_ref) :
    string =
  trait_ref_to_string fmt trait_ref

let etrait_ref_to_string (fmt : etype_formatter) (trait_ref : T.etrait_ref) :
    string =
  trait_ref_to_string fmt trait_ref

let strait_decl_ref_to_string (fmt : stype_formatter)
    (trait_decl_ref : T.strait_decl_ref) : string =
  trait_decl_ref_to_string fmt trait_decl_ref

let rtrait_decl_ref_to_string (fmt : rtype_formatter)
    (trait_decl_ref : T.rtrait_decl_ref) : string =
  trait_decl_ref_to_string fmt trait_decl_ref

let etrait_decl_ref_to_string (fmt : etype_formatter)
    (trait_decl_ref : T.etrait_decl_ref) : string =
  trait_decl_ref_to_string fmt trait_decl_ref

let sgeneric_args_to_string (fmt : stype_formatter)
    (generic_args : T.sgeneric_args) : string =
  generic_args_to_string fmt generic_args

let rgeneric_args_to_string (fmt : rtype_formatter)
    (generic_args : T.rgeneric_args) : string =
  generic_args_to_string fmt generic_args

let egeneric_args_to_string (fmt : etype_formatter)
    (generic_args : T.egeneric_args) : string =
  generic_args_to_string fmt generic_args

let strait_instance_id_to_string (fmt : stype_formatter)
    (trait_instance_id : T.strait_instance_id) : string =
  trait_instance_id_to_string fmt trait_instance_id

let rtrait_instance_id_to_string (fmt : rtype_formatter)
    (trait_instance_id : T.rtrait_instance_id) : string =
  trait_instance_id_to_string fmt trait_instance_id

let etrait_instance_id_to_string (fmt : etype_formatter)
    (trait_instance_id : T.etrait_instance_id) : string =
  trait_instance_id_to_string fmt trait_instance_id

let trait_clause_to_string (fmt : stype_formatter) (clause : T.trait_clause) :
    string =
  let clause_id = fmt.trait_clause_id_to_string clause.clause_id in
  let trait_id = fmt.trait_decl_id_to_string clause.trait_id in
  let generics = generic_args_to_string fmt clause.generics in
  "[" ^ clause_id ^ "]: " ^ trait_id ^ generics

let generic_params_to_strings (fmt : stype_formatter)
    (generics : T.generic_params) : string list * string list =
  let { T.regions; types; const_generics; trait_clauses } = generics in
  let regions = List.map region_var_to_string regions in
  let types = List.map type_var_to_string types in
  let cgs = List.map const_generic_var_to_string const_generics in
  let params = List.flatten [ regions; types; cgs ] in
  let trait_clauses = List.map (trait_clause_to_string fmt) trait_clauses in
  (params, trait_clauses)

let field_to_string fmt (f : T.field) : string =
  match f.field_name with
  | Some field_name -> field_name ^ " : " ^ ty_to_string fmt f.field_ty
  | None -> ty_to_string fmt f.field_ty

let variant_to_string fmt (v : T.variant) : string =
  v.variant_name ^ "("
  ^ String.concat ", " (List.map (field_to_string fmt) v.fields)
  ^ ")"

let trait_type_constraint_to_string (fmt : 'r type_formatter)
    (ttc : 'r T.trait_type_constraint) : string =
  let trait_ref = trait_ref_to_string fmt ttc.T.trait_ref in
  let generics = generic_args_to_string fmt ttc.T.generics in
  let ty = sty_to_string fmt ttc.T.ty in
  trait_ref ^ generics ^ " = " ^ ty

(** Helper to format "where" clauses *)
let clauses_to_string (indent : string) (indent_incr : string)
    (num_inherited_clauses : int) (clauses : string list) : string =
  let fmt_clause s = indent ^ indent_incr ^ s ^ "," in
  let clauses = List.map fmt_clause clauses in
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
let predicates_and_trait_clauses_to_string (fmt : stype_formatter)
    (indent : string) (indent_incr : string)
    (params_info : A.params_info option) (trait_clauses : string list)
    (preds : T.predicates) : string =
  let { T.regions_outlive; types_outlive; trait_type_constraints } = preds in
  let regions_outlive =
    List.map
      (fun (x, y) -> fmt.r_to_string x ^ " : " ^ fmt.r_to_string y)
      regions_outlive
  in
  let types_outlive =
    List.map
      (fun (x, y) -> sty_to_string fmt x ^ " : " ^ fmt.r_to_string y)
      types_outlive
  in
  let trait_type_constraints =
    List.map (trait_type_constraint_to_string fmt) trait_type_constraints
  in
  (* Split between the inherited clauses and the local clauses *)
  match params_info with
  | None ->
      let clauses =
        List.concat [ regions_outlive; types_outlive; trait_type_constraints ]
      in
      clauses_to_string indent indent_incr 0 clauses
  | Some pi ->
      let split_at = Collections.List.split_at in
      let trait_clauses = split_at trait_clauses pi.A.num_trait_clauses in
      let regions_outlive = split_at regions_outlive pi.A.num_regions_outlive in
      let types_outlive = split_at types_outlive pi.A.num_types_outlive in
      let ttc =
        split_at trait_type_constraints pi.A.num_trait_type_constraints
      in
      let inherited, local =
        List.split [ trait_clauses; regions_outlive; types_outlive; ttc ]
      in
      let num_inherited = List.length inherited in
      let clauses = List.concat (List.append inherited local) in
      clauses_to_string indent indent_incr num_inherited clauses

let type_decl_to_string (type_decl_id_to_string : T.TypeDeclId.id -> string)
    (global_decl_id_to_string : T.GlobalDeclId.id -> string)
    (trait_decl_id_to_string : T.TraitDeclId.id -> string)
    (trait_impl_id_to_string : T.TraitImplId.id -> string) (def : T.type_decl) :
    string =
  let regions = def.generics.regions in
  let types = def.generics.types in
  let cgs = def.generics.const_generics in
  let rid_to_string rid =
    match
      List.find_opt (fun (rv : T.region_var) -> rv.T.index = rid) regions
    with
    | Some rv -> region_var_to_string rv
    | None -> raise (Failure "Unreachable")
  in
  let r_to_string = region_to_string rid_to_string in
  let type_var_id_to_string id =
    match List.find_opt (fun (tv : T.type_var) -> tv.T.index = id) types with
    | Some tv -> type_var_to_string tv
    | None -> raise (Failure "Unreachable")
  in
  let const_generic_var_id_to_string id =
    match
      List.find_opt (fun (v : T.const_generic_var) -> v.T.index = id) cgs
    with
    | Some v -> const_generic_var_to_string v
    | None -> raise (Failure "Unreachable")
  in
  let fmt =
    {
      r_to_string;
      type_var_id_to_string;
      type_decl_id_to_string;
      const_generic_var_id_to_string;
      global_decl_id_to_string;
      trait_decl_id_to_string;
      trait_impl_id_to_string;
      trait_clause_id_to_string = trait_clause_id_to_pretty_string;
    }
  in
  let params, trait_clauses = generic_params_to_strings fmt def.generics in
  let clauses =
    predicates_and_trait_clauses_to_string fmt "" "  " None trait_clauses
      def.preds
  in
  let name = name_to_string def.name in
  let params =
    if params <> [] then "<" ^ String.concat ", " params ^ ">" else ""
  in
  match def.kind with
  | T.Struct fields ->
      if List.length fields > 0 then
        let fields =
          String.concat ","
            (List.map (fun f -> "\n  " ^ field_to_string fmt f) fields)
        in
        "struct " ^ name ^ params ^ clauses ^ "\n{" ^ fields ^ "}"
      else "struct " ^ name ^ params ^ clauses ^ "{}"
  | T.Enum variants ->
      let variants =
        List.map (fun v -> "|  " ^ variant_to_string fmt v) variants
      in
      let variants = String.concat "\n" variants in
      "enum " ^ name ^ params ^ clauses ^ "\n  =\n" ^ variants
  | T.Opaque -> "opaque type " ^ name ^ params ^ clauses

let type_ctx_to_adt_variant_to_string_fun (ctx : T.type_decl T.TypeDeclId.Map.t)
    : T.TypeDeclId.id -> T.VariantId.id -> string =
 fun def_id variant_id ->
  let def = T.TypeDeclId.Map.find def_id ctx in
  match def.kind with
  | Struct _ | Opaque -> raise (Failure "Unreachable")
  | Enum variants ->
      let variant = T.VariantId.nth variants variant_id in
      name_to_string def.name ^ "::" ^ variant.variant_name

let type_ctx_to_adt_field_names_fun (ctx : T.type_decl T.TypeDeclId.Map.t) :
    T.TypeDeclId.id -> T.VariantId.id option -> string list option =
 fun def_id opt_variant_id ->
  let def = T.TypeDeclId.Map.find def_id ctx in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  (* There are two cases: either all the fields have names, or none of them
   * has names *)
  let has_names = List.exists (fun f -> Option.is_some f.T.field_name) fields in
  if has_names then
    let fields = List.map (fun f -> Option.get f.T.field_name) fields in
    Some fields
  else None

let type_ctx_to_adt_field_to_string_fun (ctx : T.type_decl T.TypeDeclId.Map.t) :
    T.TypeDeclId.id -> T.VariantId.id option -> T.FieldId.id -> string option =
 fun def_id opt_variant_id field_id ->
  let def = T.TypeDeclId.Map.find def_id ctx in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  let field = T.FieldId.nth fields field_id in
  field.T.field_name
