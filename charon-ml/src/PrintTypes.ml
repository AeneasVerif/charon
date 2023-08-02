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

type 'r type_formatter = {
  r_to_string : 'r -> string;
  type_var_id_to_string : T.TypeVarId.id -> string;
  type_decl_id_to_string : T.TypeDeclId.id -> string;
  const_generic_var_id_to_string : T.ConstGenericVarId.id -> string;
  global_decl_id_to_string : T.GlobalDeclId.id -> string;
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
  | T.Adt (id, regions, tys, cgs) ->
      let is_tuple = match id with T.Tuple -> true | _ -> false in
      let params = params_to_string fmt is_tuple regions tys cgs in
      type_id_to_string fmt id ^ params
  | T.TypeVar tv -> fmt.type_var_id_to_string tv
  | T.Never -> "!"
  | T.Literal lit_ty -> literal_type_to_string lit_ty
  | T.Ref (r, rty, ref_kind) -> (
      match ref_kind with
      | T.Mut -> "&" ^ fmt.r_to_string r ^ " mut (" ^ ty_to_string fmt rty ^ ")"
      | T.Shared -> "&" ^ fmt.r_to_string r ^ " (" ^ ty_to_string fmt rty ^ ")")

and params_to_string (fmt : 'r type_formatter) (is_tuple : bool)
    (regions : 'r list) (types : 'r T.ty list) (cgs : T.const_generic list) :
    string =
  let regions = List.map fmt.r_to_string regions in
  let types = List.map (ty_to_string fmt) types in
  let cgs = List.map (const_generic_to_string fmt) cgs in
  let params = List.flatten [ regions; types; cgs ] in
  let params_s = String.concat ", " params in
  if is_tuple then "(" ^ params_s ^ ")"
  else if List.length params > 0 then "<" ^ params_s ^ ">"
  else ""

let sty_to_string (fmt : stype_formatter) (ty : T.sty) : string =
  ty_to_string fmt ty

let rty_to_string (fmt : rtype_formatter) (ty : T.rty) : string =
  ty_to_string fmt ty

let ety_to_string (fmt : etype_formatter) (ty : T.ety) : string =
  ty_to_string fmt ty

let field_to_string fmt (f : T.field) : string =
  match f.field_name with
  | Some field_name -> field_name ^ " : " ^ ty_to_string fmt f.field_ty
  | None -> ty_to_string fmt f.field_ty

let variant_to_string fmt (v : T.variant) : string =
  v.variant_name ^ "("
  ^ String.concat ", " (List.map (field_to_string fmt) v.fields)
  ^ ")"

let type_decl_to_string (type_decl_id_to_string : T.TypeDeclId.id -> string)
    (global_decl_id_to_string : T.GlobalDeclId.id -> string) (def : T.type_decl)
    : string =
  let regions = def.region_params in
  let types = def.type_params in
  let cgs = def.const_generic_params in
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
    }
  in
  let name = name_to_string def.name in
  let params =
    let regions = List.map region_var_to_string regions in
    let types = List.map type_var_to_string types in
    let cgs = List.map const_generic_var_to_string cgs in
    let params = List.flatten [ regions; types; cgs ] in
    if List.length params > 0 then "<" ^ String.concat ", " params ^ ">" else ""
  in
  match def.kind with
  | T.Struct fields ->
      if List.length fields > 0 then
        let fields =
          String.concat ","
            (List.map (fun f -> "\n  " ^ field_to_string fmt f) fields)
        in
        "struct " ^ name ^ params ^ "{" ^ fields ^ "}"
      else "struct " ^ name ^ params ^ "{}"
  | T.Enum variants ->
      let variants =
        List.map (fun v -> "|  " ^ variant_to_string fmt v) variants
      in
      let variants = String.concat "\n" variants in
      "enum " ^ name ^ params ^ " =\n" ^ variants
  | T.Opaque -> "opaque type " ^ name ^ params

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
