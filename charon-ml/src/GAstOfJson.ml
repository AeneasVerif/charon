(** Functions to load (U)LLBC ASTs from json.

    Initially, we used [ppx_derive_yojson] to automate this.
    However, [ppx_derive_yojson] expects formatting to be slightly
    different from what [serde_rs] generates (because it uses [Yojson.Safe.t]
    and not [Yojson.Basic.t]).

    TODO: we should check all that the integer values are in the proper range
 *)

open Yojson.Basic
open Names
open OfJsonBasic
open Identifiers
open Meta
module T = Types
module PV = PrimitiveValues
module S = Scalars
module E = Expressions
module A = GAst
module TU = TypesUtils
module AU = LlbcAstUtils
module LocalFileId = IdGen ()
module VirtualFileId = IdGen ()

(** The default logger *)
let log = Logging.llbc_of_json_logger

(** A file identifier *)
type file_id = LocalId of LocalFileId.id | VirtualId of VirtualFileId.id
[@@deriving show, ord]

module OrderedIdToFile : Collections.OrderedType with type t = file_id = struct
  type t = file_id

  let compare fid0 fid1 = compare_file_id fid0 fid1

  let to_string id =
    match id with
    | LocalId id -> "Local " ^ LocalFileId.to_string id
    | VirtualId id -> "Virtual " ^ VirtualFileId.to_string id

  let pp_t fmt x = Format.pp_print_string fmt (to_string x)
  let show_t x = to_string x
end

module IdToFile = Collections.MakeMap (OrderedIdToFile)

type id_to_file_map = file_name IdToFile.t

let file_id_of_json (js : json) : (file_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("LocalId", id) ] ->
        let* id = LocalFileId.id_of_json id in
        Ok (LocalId id)
    | `Assoc [ ("VirtualId", id) ] ->
        let* id = VirtualFileId.id_of_json id in
        Ok (VirtualId id)
    | _ -> Error "")

let file_name_of_json (js : json) : (file_name, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Virtual", name) ] ->
        let* name = string_of_json name in
        Ok (Virtual name)
    | `Assoc [ ("Local", name) ] ->
        let* name = string_of_json name in
        Ok (Local name)
    | _ -> Error "")

(** Deserialize a map from file id to file name.

    In the serialized LLBC, the files in the loc spans are refered to by their
    ids, in order to save space. In a functional language like OCaml this is
    not necessary: we thus replace the file ids by the file name themselves in
    the AST.
    The "id to file" map is thus only used in the deserialization process.
  *)
let id_to_file_of_json (js : json) : (id_to_file_map, string) result =
  combine_error_msgs js __FUNCTION__
    ((* The map is stored as a list of pairs (key, value): we deserialize
      * this list then convert it to a map *)
     let* key_values =
       list_of_json (pair_of_json file_id_of_json file_name_of_json) js
     in
     Ok (IdToFile.of_list key_values))

let loc_of_json (js : json) : (loc, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("line", line); ("col", col) ] ->
        let* line = int_of_json line in
        let* col = int_of_json col in
        Ok { line; col }
    | _ -> Error "")

let span_of_json (id_to_file : id_to_file_map) (js : json) :
    (span, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("file_id", file_id); ("beg", beg_loc); ("end", end_loc) ] ->
        let* file_id = file_id_of_json file_id in
        let file = IdToFile.find file_id id_to_file in
        let* beg_loc = loc_of_json beg_loc in
        let* end_loc = loc_of_json end_loc in
        Ok { file; beg_loc; end_loc }
    | _ -> Error "")

let meta_of_json (id_to_file : id_to_file_map) (js : json) :
    (meta, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("generated_from_span", generated_from_span) ] ->
        let* span = span_of_json id_to_file span in
        let* generated_from_span =
          option_of_json (span_of_json id_to_file) generated_from_span
        in
        Ok { span; generated_from_span }
    | _ -> Error "")

let path_elem_of_json (js : json) : (path_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ident", name) ] ->
        let* name = string_of_json name in
        Ok (Ident name)
    | `Assoc [ ("Disambiguator", d) ] ->
        let* d = Disambiguator.id_of_json d in
        Ok (Disambiguator d)
    | _ -> Error "")

let name_of_json (js : json) : (name, string) result =
  combine_error_msgs js __FUNCTION__ (list_of_json path_elem_of_json js)

let fun_name_of_json (js : json) : (fun_name, string) result =
  combine_error_msgs js __FUNCTION__ (name_of_json js)

let type_var_of_json (js : json) : (T.type_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = T.TypeVarId.id_of_json index in
        let* name = string_of_json name in
        Ok { T.index; name }
    | _ -> Error "")

let region_var_of_json (js : json) : (T.region_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = T.RegionVarId.id_of_json index in
        let* name = string_option_of_json name in
        Ok { T.index; name }
    | _ -> Error "")

let region_of_json (js : json) : (T.RegionVarId.id T.region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Static" -> Ok T.Static
    | `Assoc [ ("Var", rid) ] ->
        let* rid = T.RegionVarId.id_of_json rid in
        Ok (T.Var rid : T.RegionVarId.id T.region)
    | _ -> Error "")

let erased_region_of_json (js : json) : (T.erased_region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with `String "Erased" -> Ok T.Erased | _ -> Error "")

let integer_type_of_json (js : json) : (PV.integer_type, string) result =
  match js with
  | `String "Isize" -> Ok PV.Isize
  | `String "I8" -> Ok PV.I8
  | `String "I16" -> Ok PV.I16
  | `String "I32" -> Ok PV.I32
  | `String "I64" -> Ok PV.I64
  | `String "I128" -> Ok PV.I128
  | `String "Usize" -> Ok PV.Usize
  | `String "U8" -> Ok PV.U8
  | `String "U16" -> Ok PV.U16
  | `String "U32" -> Ok PV.U32
  | `String "U64" -> Ok PV.U64
  | `String "U128" -> Ok PV.U128
  | _ -> Error ("integer_type_of_json failed on: " ^ show js)

let literal_type_of_json (js : json) : (PV.literal_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Integer", int_ty) ] ->
        let* int_ty = integer_type_of_json int_ty in
        Ok (PV.Integer int_ty)
    | `String "Bool" -> Ok PV.Bool
    | `String "Char" -> Ok PV.Char
    | _ -> Error "")

let const_generic_var_of_json (js : json) : (T.const_generic_var, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = T.ConstGenericVarId.id_of_json index in
        let* name = string_of_json name in
        let* ty = literal_type_of_json ty in
        Ok { T.index; name; ty }
    | _ -> Error "")

let ref_kind_of_json (js : json) : (T.ref_kind, string) result =
  match js with
  | `String "Mut" -> Ok T.Mut
  | `String "Shared" -> Ok T.Shared
  | _ -> Error ("ref_kind_of_json failed on: " ^ show js)

let assumed_ty_of_json (js : json) : (T.assumed_ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Box" -> Ok T.Box
    | `String "Vec" -> Ok T.Vec
    | `String "Option" -> Ok T.Option
    | `String "Array" -> Ok T.Array
    | `String "Slice" -> Ok T.Slice
    | `String "Str" -> Ok T.Str
    | `String "Range" -> Ok T.Range
    | _ -> Error "")

let type_id_of_json (js : json) : (T.type_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", id) ] ->
        let* id = T.TypeDeclId.id_of_json id in
        Ok (T.AdtId id)
    | `String "Tuple" -> Ok T.Tuple
    | `Assoc [ ("Assumed", aty) ] ->
        let* aty = assumed_ty_of_json aty in
        Ok (T.Assumed aty)
    | _ -> Error "")

let big_int_of_json (js : json) : (PV.big_int, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Int i -> Ok (Z.of_int i)
    | `String is -> Ok (Z.of_string is)
    | _ -> Error "")

(** Deserialize a {!PV.scalar_value} from JSON and **check the ranges**.

    Note that in practice we also check that the values are in range
    in the interpreter functions. Still, it doesn't cost much to be
    a bit conservative.
 *)
let scalar_value_of_json (js : json) : (PV.scalar_value, string) result =
  let res =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("Isize", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = Isize }
      | `Assoc [ ("I8", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = I8 }
      | `Assoc [ ("I16", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = I16 }
      | `Assoc [ ("I32", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = I32 }
      | `Assoc [ ("I64", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = I64 }
      | `Assoc [ ("I128", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = I128 }
      | `Assoc [ ("Usize", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = Usize }
      | `Assoc [ ("U8", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = U8 }
      | `Assoc [ ("U16", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = U16 }
      | `Assoc [ ("U32", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = U32 }
      | `Assoc [ ("U64", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = U64 }
      | `Assoc [ ("U128", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { PV.value = bi; int_ty = U128 }
      | _ -> Error "")
  in
  match res with
  | Error _ -> res
  | Ok sv ->
      if not (S.check_scalar_value_in_range sv) then (
        log#serror ("Scalar value not in range: " ^ PV.show_scalar_value sv);
        raise
          (Failure ("Scalar value not in range: " ^ PV.show_scalar_value sv)));
      res

let literal_of_json (js : json) : (PV.literal, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", v) ] ->
        let* v = scalar_value_of_json v in
        Ok (PV.Scalar v)
    | `Assoc [ ("Bool", v) ] ->
        let* v = bool_of_json v in
        Ok (PV.Bool v)
    | `Assoc [ ("Char", v) ] ->
        let* v = char_of_json v in
        Ok (PV.Char v)
    | _ -> Error "")

let const_generic_of_json (js : json) : (T.const_generic, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Global", id) ] ->
        let* id = E.GlobalDeclId.id_of_json id in
        Ok (T.ConstGenericGlobal id)
    | `Assoc [ ("Var", id) ] ->
        let* id = T.ConstGenericVarId.id_of_json id in
        Ok (T.ConstGenericVar id)
    | `Assoc [ ("Value", lit) ] ->
        let* lit = literal_of_json lit in
        Ok (T.ConstGenericValue lit)
    | _ -> Error "")

let rec ty_of_json (r_of_json : json -> ('r, string) result) (js : json) :
    ('r T.ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ id; generics ]) ] ->
        let* id = type_id_of_json id in
        let* generics = generic_args_of_json r_of_json generics in
        (* Sanity check *)
        (match id with
        | T.Tuple ->
            assert (generics.T.regions = [] && generics.T.trait_refs = [])
        | _ -> ());
        Ok (T.Adt (id, generics))
    | `Assoc [ ("TypeVar", id) ] ->
        let* id = T.TypeVarId.id_of_json id in
        Ok (T.TypeVar id)
    | `Assoc [ ("Literal", ty) ] ->
        let* ty = literal_type_of_json ty in
        Ok (T.Literal ty)
    | `Assoc [ ("Ref", `List [ region; ty; ref_kind ]) ] ->
        let* region = r_of_json region in
        let* ty = ty_of_json r_of_json ty in
        let* ref_kind = ref_kind_of_json ref_kind in
        Ok (T.Ref (region, ty, ref_kind))
    | `Assoc [ ("TraitType", `List [ trait_ref; generics; item_name ]) ] ->
        let* trait_ref = trait_ref_of_json r_of_json trait_ref in
        let* generics = generic_args_of_json r_of_json generics in
        let* item_name = string_of_json item_name in
        Ok (T.TraitType (trait_ref, generics, item_name))
    | _ -> Error "")

and trait_ref_of_json (r_of_json : json -> ('r, string) result) (js : json) :
    ('r T.trait_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("trait_id", trait_id);
          ("generics", generics);
          ("trait_decl_ref", trait_decl_ref);
        ] ->
        let* trait_id = trait_instance_id_of_json r_of_json trait_id in
        let* generics = generic_args_of_json r_of_json generics in
        let* trait_decl_ref = trait_decl_ref_of_json r_of_json trait_decl_ref in
        Ok ({ trait_id; generics; trait_decl_ref } : 'r T.trait_ref)
    | _ -> Error "")

and trait_decl_ref_of_json (r_of_json : json -> ('r, string) result) (js : json)
    : ('r T.trait_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("trait_id", trait_id); ("generics", generics) ] ->
        let* trait_decl_id = T.TraitDeclId.id_of_json trait_id in
        let* decl_generics = generic_args_of_json r_of_json generics in
        Ok ({ trait_decl_id; decl_generics } : 'r T.trait_decl_ref)
    | _ -> Error "")

and generic_args_of_json (r_of_json : json -> ('r, string) result) (js : json) :
    ('r T.generic_args, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("regions", regions);
          ("types", types);
          ("const_generics", const_generics);
          ("trait_refs", trait_refs);
        ] ->
        let* regions = list_of_json r_of_json regions in
        let* types = list_of_json (ty_of_json r_of_json) types in
        let* const_generics =
          list_of_json const_generic_of_json const_generics
        in
        let* trait_refs =
          list_of_json (trait_ref_of_json r_of_json) trait_refs
        in
        Ok { T.regions; types; const_generics; trait_refs }
    | _ -> Error "")

and trait_instance_id_of_json (r_of_json : json -> ('r, string) result)
    (js : json) : ('r T.trait_instance_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "SelfId" -> Ok T.Self
    | `Assoc [ ("TraitImpl", id) ] ->
        let* id = T.TraitImplId.id_of_json id in
        Ok (T.TraitImpl id)
    | `Assoc [ ("BuiltinOrAuto", id) ] ->
        let* id = T.TraitDeclId.id_of_json id in
        Ok (T.BuiltinOrAuto id)
    | `Assoc [ ("Clause", id) ] ->
        let* id = T.TraitClauseId.id_of_json id in
        Ok (T.Clause id)
    | `Assoc [ ("ParentClause", `List [ inst_id; decl_id; clause_id ]) ] ->
        let* inst_id = trait_instance_id_of_json r_of_json inst_id in
        let* decl_id = T.TraitDeclId.id_of_json decl_id in
        let* clause_id = T.TraitClauseId.id_of_json clause_id in
        Ok (T.ParentClause (inst_id, decl_id, clause_id))
    | `Assoc
        [ ("ItemClause", `List [ inst_id; decl_id; item_name; clause_id ]) ] ->
        let* inst_id = trait_instance_id_of_json r_of_json inst_id in
        let* decl_id = T.TraitDeclId.id_of_json decl_id in
        let* item_name = string_of_json item_name in
        let* clause_id = T.TraitClauseId.id_of_json clause_id in
        Ok (T.ItemClause (inst_id, decl_id, item_name, clause_id))
    | _ -> Error "")

let sty_of_json (js : json) : (T.sty, string) result =
  combine_error_msgs js __FUNCTION__ (ty_of_json region_of_json js)

let ety_of_json (js : json) : (T.ety, string) result =
  combine_error_msgs js __FUNCTION__ (ty_of_json erased_region_of_json js)

let sgeneric_args_of_json (js : json) : (T.sgeneric_args, string) result =
  combine_error_msgs js __FUNCTION__ (generic_args_of_json region_of_json js)

let egeneric_args_of_json (js : json) : (T.egeneric_args, string) result =
  combine_error_msgs js __FUNCTION__
    (generic_args_of_json erased_region_of_json js)

let strait_ref_of_json (js : json) : (T.strait_ref, string) result =
  combine_error_msgs js __FUNCTION__ (trait_ref_of_json region_of_json js)

let etrait_ref_of_json (js : json) : (T.etrait_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (trait_ref_of_json erased_region_of_json js)

let strait_decl_ref_of_json (js : json) : (T.strait_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__ (trait_decl_ref_of_json region_of_json js)

let etrait_decl_ref_of_json (js : json) : (T.etrait_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (trait_decl_ref_of_json erased_region_of_json js)

let field_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.field, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("name", name); ("ty", ty) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* name = option_of_json string_of_json name in
        let* ty = sty_of_json ty in
        Ok { T.meta; field_name = name; field_ty = ty }
    | _ -> Error "")

let variant_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.variant, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("name", name); ("fields", fields) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* name = string_of_json name in
        let* fields = list_of_json (field_of_json id_to_file) fields in
        Ok { T.meta; variant_name = name; fields }
    | _ -> Error "")

let type_decl_kind_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.type_decl_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Struct", fields) ] ->
        let* fields = list_of_json (field_of_json id_to_file) fields in
        Ok (T.Struct fields)
    | `Assoc [ ("Enum", variants) ] ->
        let* variants = list_of_json (variant_of_json id_to_file) variants in
        Ok (T.Enum variants)
    | `String "Opaque" -> Ok T.Opaque
    | _ -> Error "")

let region_var_group_of_json (js : json) : (T.region_var_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("regions", regions); ("parents", parents) ] ->
        let* id = T.RegionGroupId.id_of_json id in
        let* regions = list_of_json T.RegionVarId.id_of_json regions in
        let* parents = list_of_json T.RegionGroupId.id_of_json parents in
        Ok { T.id; regions; parents }
    | _ -> Error "")

let region_var_groups_of_json (js : json) : (T.region_var_groups, string) result
    =
  combine_error_msgs js __FUNCTION__ (list_of_json region_var_group_of_json js)

let trait_clause_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.trait_clause, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("clause_id", clause_id);
          ("meta", meta);
          ("trait_id", trait_id);
          ("generics", generics);
        ] ->
        let* clause_id = T.TraitClauseId.id_of_json clause_id in
        let* meta = meta_of_json id_to_file meta in
        let* trait_id = T.TraitDeclId.id_of_json trait_id in
        let* generics = sgeneric_args_of_json generics in
        Ok ({ clause_id; meta; trait_id; generics } : T.trait_clause)
    | _ -> Error "")

let generic_params_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.generic_params, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("regions", regions);
          ("types", types);
          ("const_generics", const_generics);
          ("trait_clauses", trait_clauses);
        ] ->
        let* regions = list_of_json region_var_of_json regions in
        let* types = list_of_json type_var_of_json types in
        let* const_generics =
          list_of_json const_generic_var_of_json const_generics
        in
        let* trait_clauses =
          list_of_json (trait_clause_of_json id_to_file) trait_clauses
        in
        Ok { T.regions; types; const_generics; trait_clauses }
    | _ -> Error "")

let region_outlives_of_json (js : json) : (T.region_outlives, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List [ r0; r1 ] ->
        let* r0 = region_of_json r0 in
        let* r1 = region_of_json r1 in
        Ok (r0, r1)
    | _ -> Error "")

let type_outlives_of_json (js : json) : (T.type_outlives, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List [ ty; r ] ->
        let* ty = sty_of_json ty in
        let* r = region_of_json r in
        Ok (ty, r)
    | _ -> Error "")

let trait_type_constraint_of_json (r_of_json : json -> ('r, string) result)
    (js : json) : ('r T.trait_type_constraint, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("trait_ref", trait_ref);
          ("generics", generics);
          ("type_name", type_name);
          ("ty", ty);
        ] ->
        let* trait_ref = trait_ref_of_json r_of_json trait_ref in
        let* generics = generic_args_of_json r_of_json generics in
        let* type_name = string_of_json type_name in
        let* ty = ty_of_json r_of_json ty in
        Ok
          ({ T.trait_ref; generics; type_name; ty }
            : 'r T.trait_type_constraint)
    | _ -> Error "")

let predicates_of_json (js : json) : (T.predicates, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("regions_outlive", regions_outlive);
          ("types_outlive", types_outlive);
          ("trait_type_constraints", trait_type_constraints);
        ] ->
        let* regions_outlive =
          list_of_json region_outlives_of_json regions_outlive
        in
        let* types_outlive = list_of_json type_outlives_of_json types_outlive in
        let* trait_type_constraints =
          list_of_json
            (trait_type_constraint_of_json region_of_json)
            trait_type_constraints
        in
        Ok { T.regions_outlive; types_outlive; trait_type_constraints }
    | _ -> Error "")

let type_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.type_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("meta", meta);
          ("name", name);
          ("generics", generics);
          ("preds", preds);
          ("kind", kind);
          ("regions_hierarchy", regions_hierarchy);
        ] ->
        let* def_id = T.TypeDeclId.id_of_json def_id in
        let* meta = meta_of_json id_to_file meta in
        let* name = name_of_json name in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* kind = type_decl_kind_of_json id_to_file kind in
        let* regions_hierarchy = region_var_groups_of_json regions_hierarchy in
        Ok { T.def_id; meta; name; generics; preds; kind; regions_hierarchy }
    | _ -> Error "")

let var_of_json (js : json) : (A.var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = E.VarId.id_of_json index in
        let* name = string_option_of_json name in
        let* var_ty = ety_of_json ty in
        Ok { A.index; name; var_ty }
    | _ -> Error "")

let field_proj_kind_of_json (js : json) : (E.field_proj_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("ProjAdt", `List [ def_id; opt_variant_id ]) ] ->
        let* def_id = T.TypeDeclId.id_of_json def_id in
        let* opt_variant_id =
          option_of_json T.VariantId.id_of_json opt_variant_id
        in
        Ok (E.ProjAdt (def_id, opt_variant_id))
    | `Assoc [ ("ProjTuple", i) ] ->
        let* i = int_of_json i in
        Ok (E.ProjTuple i)
    | `Assoc [ ("ProjOption", variant_id) ] ->
        let* variant_id = T.VariantId.id_of_json variant_id in
        Ok (E.ProjOption variant_id)
    | _ -> Error "")

let projection_elem_of_json (js : json) : (E.projection_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Deref" -> Ok E.Deref
    | `String "DerefBox" -> Ok E.DerefBox
    | `Assoc [ ("Field", `List [ proj_kind; field_id ]) ] ->
        let* proj_kind = field_proj_kind_of_json proj_kind in
        let* field_id = T.FieldId.id_of_json field_id in
        Ok (E.Field (proj_kind, field_id))
    | _ -> Error ("projection_elem_of_json failed on:" ^ show js))

let projection_of_json (js : json) : (E.projection, string) result =
  combine_error_msgs js __FUNCTION__ (list_of_json projection_elem_of_json js)

let place_of_json (js : json) : (E.place, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("var_id", var_id); ("projection", projection) ] ->
        let* var_id = E.VarId.id_of_json var_id in
        let* projection = projection_of_json projection in
        Ok { E.var_id; projection }
    | _ -> Error "")

let borrow_kind_of_json (js : json) : (E.borrow_kind, string) result =
  match js with
  | `String "Shared" -> Ok E.Shared
  | `String "Mut" -> Ok E.Mut
  | `String "TwoPhaseMut" -> Ok E.TwoPhaseMut
  | `String "Shallow" -> Ok E.Shallow
  | _ -> Error ("borrow_kind_of_json failed on:" ^ show js)

let unop_of_json (js : json) : (E.unop, string) result =
  match js with
  | `String "Not" -> Ok E.Not
  | `String "Neg" -> Ok E.Neg
  | `Assoc [ ("Cast", `List [ src_ty; tgt_ty ]) ] ->
      let* src_ty = integer_type_of_json src_ty in
      let* tgt_ty = integer_type_of_json tgt_ty in
      Ok (E.Cast (src_ty, tgt_ty))
  | _ -> Error ("unop_of_json failed on:" ^ show js)

let binop_of_json (js : json) : (E.binop, string) result =
  match js with
  | `String "BitXor" -> Ok E.BitXor
  | `String "BitAnd" -> Ok E.BitAnd
  | `String "BitOr" -> Ok E.BitOr
  | `String "Eq" -> Ok E.Eq
  | `String "Lt" -> Ok E.Lt
  | `String "Le" -> Ok E.Le
  | `String "Ne" -> Ok E.Ne
  | `String "Ge" -> Ok E.Ge
  | `String "Gt" -> Ok E.Gt
  | `String "Div" -> Ok E.Div
  | `String "Rem" -> Ok E.Rem
  | `String "Add" -> Ok E.Add
  | `String "Sub" -> Ok E.Sub
  | `String "Mul" -> Ok E.Mul
  | `String "Shl" -> Ok E.Shl
  | `String "Shr" -> Ok E.Shr
  | _ -> Error ("binop_of_json failed on:" ^ show js)

let literal_of_json (js : json) : (PV.literal, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", scalar_value) ] ->
        let* scalar_value = scalar_value_of_json scalar_value in
        Ok (PV.Scalar scalar_value)
    | `Assoc [ ("Bool", v) ] ->
        let* v = bool_of_json v in
        Ok (PV.Bool v)
    | `Assoc [ ("Char", v) ] ->
        let* v = char_of_json v in
        Ok (PV.Char v)
    | _ -> Error "")

let rec constant_expr_of_json (js : json) : (E.constant_expr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("value", value); ("ty", ty) ] ->
        let* value = raw_constant_expr_of_json value in
        let* ty = ety_of_json ty in
        Ok { E.value; E.ty }
    | _ -> Error "")

and raw_constant_expr_of_json (js : json) : (E.raw_constant_expr, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Literal", lit) ] ->
        let* lit = literal_of_json lit in
        Ok (E.CLiteral lit)
    | `Assoc [ ("Var", vid) ] ->
        let* vid = T.ConstGenericVarId.id_of_json vid in
        Ok (E.CVar vid)
    | `Assoc [ ("TraitConst", `List [ trait_ref; generics; const_name ]) ] ->
        let* trait_ref = etrait_ref_of_json trait_ref in
        let* generics = egeneric_args_of_json generics in
        let* const_name = string_of_json const_name in
        Ok (E.TraitConst (trait_ref, generics, const_name))
    | _ -> Error "")

let operand_of_json (js : json) : (E.operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Copy", place) ] ->
        let* place = place_of_json place in
        Ok (E.Copy place)
    | `Assoc [ ("Move", place) ] ->
        let* place = place_of_json place in
        Ok (E.Move place)
    | `Assoc [ ("Const", cv) ] ->
        let* cv = constant_expr_of_json cv in
        Ok (E.Constant cv)
    | _ -> Error "")

let aggregate_kind_of_json (js : json) : (E.aggregate_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Tuple" -> Ok E.AggregatedTuple
    | `Assoc [ ("Option", `List [ variant_id; ty ]) ] ->
        let* variant_id = T.VariantId.id_of_json variant_id in
        let* ty = ety_of_json ty in
        Ok (E.AggregatedOption (variant_id, ty))
    | `Assoc [ ("Adt", `List [ id; opt_variant_id; generics ]) ] ->
        let* id = T.TypeDeclId.id_of_json id in
        let* opt_variant_id =
          option_of_json T.VariantId.id_of_json opt_variant_id
        in
        let* generics = egeneric_args_of_json generics in
        Ok (E.AggregatedAdt (id, opt_variant_id, generics))
    | `Assoc [ ("Range", ty) ] ->
        let* ty = ety_of_json ty in
        Ok (E.AggregatedRange ty)
    | `Assoc [ ("Array", `List [ ty; cg ]) ] ->
        let* ty = ety_of_json ty in
        let* cg = const_generic_of_json cg in
        Ok (E.AggregatedArray (ty, cg))
    | _ -> Error "")

let rvalue_of_json (js : json) : (E.rvalue, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Use", op) ] ->
        let* op = operand_of_json op in
        Ok (E.Use op)
    | `Assoc [ ("Ref", `List [ place; borrow_kind ]) ] ->
        let* place = place_of_json place in
        let* borrow_kind = borrow_kind_of_json borrow_kind in
        Ok (E.RvRef (place, borrow_kind))
    | `Assoc [ ("UnaryOp", `List [ unop; op ]) ] ->
        let* unop = unop_of_json unop in
        let* op = operand_of_json op in
        Ok (E.UnaryOp (unop, op))
    | `Assoc [ ("BinaryOp", `List [ binop; op1; op2 ]) ] ->
        let* binop = binop_of_json binop in
        let* op1 = operand_of_json op1 in
        let* op2 = operand_of_json op2 in
        Ok (E.BinaryOp (binop, op1, op2))
    | `Assoc [ ("Discriminant", place) ] ->
        let* place = place_of_json place in
        Ok (E.Discriminant place)
    | `Assoc [ ("Global", gid) ] ->
        let* gid = E.GlobalDeclId.id_of_json gid in
        Ok (E.Global gid)
    | `Assoc [ ("Aggregate", `List [ aggregate_kind; ops ]) ] ->
        let* aggregate_kind = aggregate_kind_of_json aggregate_kind in
        let* ops = list_of_json operand_of_json ops in
        Ok (E.Aggregate (aggregate_kind, ops))
    | _ -> Error "")

let assumed_fun_id_of_json (js : json) : (A.assumed_fun_id, string) result =
  match js with
  | `String "Replace" -> Ok A.Replace
  | `String "BoxNew" -> Ok A.BoxNew
  | `String "BoxDeref" -> Ok A.BoxDeref
  | `String "BoxDerefMut" -> Ok A.BoxDerefMut
  | `String "BoxFree" -> Ok A.BoxFree
  | `String "VecNew" -> Ok A.VecNew
  | `String "VecPush" -> Ok A.VecPush
  | `String "VecInsert" -> Ok A.VecInsert
  | `String "VecLen" -> Ok A.VecLen
  | `String "VecIndex" -> Ok A.VecIndex
  | `String "VecIndexMut" -> Ok A.VecIndexMut
  | `String "ArrayIndexShared" -> Ok A.ArrayIndexShared
  | `String "ArrayIndexMut" -> Ok A.ArrayIndexMut
  | `String "ArrayToSliceShared" -> Ok A.ArrayToSliceShared
  | `String "ArrayToSliceMut" -> Ok A.ArrayToSliceMut
  | `String "ArraySubsliceShared" -> Ok A.ArraySubsliceShared
  | `String "ArraySubsliceMut" -> Ok A.ArraySubsliceMut
  | `String "SliceLen" -> Ok A.SliceLen
  | `String "SliceIndexShared" -> Ok A.SliceIndexShared
  | `String "SliceIndexMut" -> Ok A.SliceIndexMut
  | `String "SliceSubsliceShared" -> Ok A.SliceSubsliceShared
  | `String "SliceSubsliceMut" -> Ok A.SliceSubsliceMut
  | _ -> Error ("assumed_fun_id_of_json failed on:" ^ show js)

let fun_id_of_json (js : json) : (A.fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", id) ] ->
        let* id = A.FunDeclId.id_of_json id in
        Ok (A.Regular id)
    | `Assoc [ ("Assumed", fid) ] ->
        let* fid = assumed_fun_id_of_json fid in
        Ok (A.Assumed fid)
    | _ -> Error "")

let params_info_of_json (js : json) : (A.params_info, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("num_region_params", num_region_params);
          ("num_type_params", num_type_params);
          ("num_const_generic_params", num_const_generic_params);
          ("num_trait_clauses", num_trait_clauses);
          ("num_regions_outlive", num_regions_outlive);
          ("num_types_outlive", num_types_outlive);
          ("num_trait_type_constraints", num_trait_type_constraints);
        ] ->
        let* num_region_params = int_of_json num_region_params in
        let* num_type_params = int_of_json num_type_params in
        let* num_const_generic_params = int_of_json num_const_generic_params in
        let* num_trait_clauses = int_of_json num_trait_clauses in
        let* num_regions_outlive = int_of_json num_regions_outlive in
        let* num_types_outlive = int_of_json num_types_outlive in
        let* num_trait_type_constraints =
          int_of_json num_trait_type_constraints
        in
        Ok
          {
            A.num_region_params;
            num_type_params;
            num_const_generic_params;
            num_trait_clauses;
            num_regions_outlive;
            num_types_outlive;
            num_trait_type_constraints;
          }
    | _ -> Error "")

let fun_sig_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.fun_sig, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("generics", generics);
          ("preds", preds);
          ("parent_params_info", parent_params_info);
          ("inputs", inputs);
          ("output", output);
          ("regions_hierarchy", regions_hierarchy);
        ] ->
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* parent_params_info =
          option_of_json params_info_of_json parent_params_info
        in
        let* inputs = list_of_json sty_of_json inputs in
        let* output = sty_of_json output in
        let* regions_hierarchy = region_var_groups_of_json regions_hierarchy in
        Ok
          {
            A.generics;
            preds;
            parent_params_info;
            inputs;
            output;
            regions_hierarchy;
          }
    | _ -> Error "")

let fun_id_or_trait_method_ref_of_json (js : json) :
    (A.fun_id_or_trait_method_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Fun", id) ] ->
        let* id = fun_id_of_json id in
        Ok (A.FunId id)
    | `Assoc [ ("Trait", `List [ trait_ref; method_name; fun_decl_id ]) ] ->
        let* trait_ref = etrait_ref_of_json trait_ref in
        let* method_name = string_of_json method_name in
        let* fun_decl_id = A.FunDeclId.id_of_json fun_decl_id in
        Ok (A.TraitMethod (trait_ref, method_name, fun_decl_id))
    | _ -> Error "")

let call_of_json (js : json) : (A.call, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("func", func);
          ("generics", generics);
          ("trait_and_method_generic_args", trait_and_method_generic_args);
          ("args", args);
          ("dest", dest);
        ] ->
        let* func = fun_id_or_trait_method_ref_of_json func in
        let* generics = egeneric_args_of_json generics in
        let* trait_and_method_generic_args =
          option_of_json egeneric_args_of_json trait_and_method_generic_args
        in
        let* args = list_of_json operand_of_json args in
        let* dest = place_of_json dest in
        Ok { A.func; generics; trait_and_method_generic_args; args; dest }
    | _ -> Error "")

let gexpr_body_of_json (body_of_json : json -> ('body, string) result)
    (id_to_file : id_to_file_map) (js : json) :
    ('body A.gexpr_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("meta", meta);
          ("arg_count", arg_count);
          ("locals", locals);
          ("body", body);
        ] ->
        let* meta = meta_of_json id_to_file meta in
        let* arg_count = int_of_json arg_count in
        let* locals = list_of_json var_of_json locals in
        let* body = body_of_json body in
        Ok { A.meta; arg_count; locals; body }
    | _ -> Error "")

let fun_kind_of_json (js : json) : (A.fun_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Regular" -> Ok A.RegularKind
    | `Assoc
        [
          ( "TraitMethodImpl",
            `Assoc
              [
                ("trait_id", trait_id);
                ("method_name", method_name);
                ("provided", provided);
              ] );
        ] ->
        let* trait_id = A.TraitDeclId.id_of_json trait_id in
        let* method_name = string_of_json method_name in
        let* provided = bool_of_json provided in
        Ok (A.TraitMethodImpl (trait_id, method_name, provided))
    | `Assoc [ ("TraitMethodDecl", `List [ trait_id; item_name ]) ] ->
        let* trait_id = A.TraitDeclId.id_of_json trait_id in
        let* item_name = string_of_json item_name in
        Ok (A.TraitMethodDecl (trait_id, item_name))
    | `Assoc [ ("TraitMethodProvided", `List [ trait_id; item_name ]) ] ->
        let* trait_id = A.TraitDeclId.id_of_json trait_id in
        let* item_name = string_of_json item_name in
        Ok (A.TraitMethodProvided (trait_id, item_name))
    | _ -> Error "")

let gfun_decl_of_json (body_of_json : json -> ('body, string) result)
    (id_to_file : id_to_file_map) (js : json) :
    ('body A.gfun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("meta", meta);
          ("name", name);
          ("signature", signature);
          ("kind", kind);
          ("body", body);
        ] ->
        let* def_id = A.FunDeclId.id_of_json def_id in
        let* meta = meta_of_json id_to_file meta in
        let* name = fun_name_of_json name in
        let* signature = fun_sig_of_json id_to_file signature in
        let* kind = fun_kind_of_json kind in
        let* body =
          option_of_json (gexpr_body_of_json body_of_json id_to_file) body
        in
        Ok
          {
            A.def_id;
            meta;
            name;
            signature;
            kind;
            body;
            is_global_decl_body = false;
          }
    | _ -> Error "")

(** Auxiliary definition, which we use only for deserialization purposes *)
type 'body gglobal_decl = {
  def_id : A.GlobalDeclId.id;
  meta : meta;
  body : 'body A.gexpr_body option;
  name : global_name;
  ty : T.ety;
}
[@@deriving show]

let gglobal_decl_of_json (body_of_json : json -> ('body, string) result)
    (id_to_file : id_to_file_map) (js : json) :
    ('body gglobal_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("meta", meta);
          ("name", name);
          ("ty", ty);
          ("body", body);
        ] ->
        let* global_id = A.GlobalDeclId.id_of_json def_id in
        let* meta = meta_of_json id_to_file meta in
        let* name = fun_name_of_json name in
        let* ty = ety_of_json ty in
        let* body =
          option_of_json (gexpr_body_of_json body_of_json id_to_file) body
        in
        Ok { def_id = global_id; meta; body; name; ty }
    | _ -> Error "")

let trait_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.trait_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("name", name);
          ("generics", generics);
          ("preds", preds);
          ("all_trait_clauses", all_trait_clauses);
          ("consts", consts);
          ("types", types);
          ("required_methods", required_methods);
          ("provided_methods", provided_methods);
        ] ->
        let* def_id = A.TraitDeclId.id_of_json def_id in
        let* name = name_of_json name in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* all_trait_clauses =
          list_of_json (trait_clause_of_json id_to_file) all_trait_clauses
        in
        let* consts =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json ety_of_json
                  (option_of_json A.GlobalDeclId.id_of_json)))
            consts
        in
        let* types =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json
                  (list_of_json (trait_clause_of_json id_to_file))
                  (option_of_json ety_of_json)))
            types
        in
        let* required_methods =
          list_of_json
            (pair_of_json string_of_json A.FunDeclId.id_of_json)
            required_methods
        in
        let* provided_methods =
          list_of_json
            (pair_of_json string_of_json
               (option_of_json A.FunDeclId.id_of_json))
            provided_methods
        in
        Ok
          {
            A.def_id;
            name;
            generics;
            preds;
            all_trait_clauses;
            consts;
            types;
            required_methods;
            provided_methods;
          }
    | _ -> Error "")

let trait_impl_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.trait_impl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("name", name);
          ("impl_trait", impl_trait);
          ("generics", generics);
          ("preds", preds);
          ("consts", consts);
          ("types", types);
          ("required_methods", required_methods);
          ("provided_methods", provided_methods);
        ] ->
        let* def_id = A.TraitImplId.id_of_json def_id in
        let* name = name_of_json name in
        let* impl_trait = strait_decl_ref_of_json impl_trait in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* consts =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json ety_of_json A.GlobalDeclId.id_of_json))
            consts
        in
        let* types =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json (list_of_json etrait_ref_of_json) ety_of_json))
            types
        in
        let methods_of_json =
          list_of_json (pair_of_json string_of_json A.FunDeclId.id_of_json)
        in
        let* required_methods = methods_of_json required_methods in
        let* provided_methods = methods_of_json provided_methods in
        Ok
          ({
             A.def_id;
             name;
             impl_trait;
             generics;
             preds;
             consts;
             types;
             required_methods;
             provided_methods;
           }
            : A.trait_impl)
    | _ -> Error "")

let g_declaration_group_of_json (id_of_json : json -> ('id, string) result)
    (js : json) : ('id A.g_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("NonRec", id) ] ->
        let* id = id_of_json id in
        Ok (A.NonRec id)
    | `Assoc [ ("Rec", ids) ] ->
        let* ids = list_of_json id_of_json ids in
        Ok (A.Rec ids)
    | _ -> Error "")

let type_declaration_group_of_json (js : json) :
    (A.type_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (g_declaration_group_of_json T.TypeDeclId.id_of_json js)

let fun_declaration_group_of_json (js : json) :
    (A.fun_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (g_declaration_group_of_json A.FunDeclId.id_of_json js)

let global_declaration_group_of_json (js : json) :
    (A.GlobalDeclId.id, string) result =
  combine_error_msgs js __FUNCTION__
    (let* decl = g_declaration_group_of_json A.GlobalDeclId.id_of_json js in
     match decl with
     | NonRec id -> Ok id
     | Rec _ -> Error "got mutually dependent globals")

let trait_declaration_group_of_json (js : json) :
    (A.TraitDeclId.id, string) result =
  combine_error_msgs js __FUNCTION__
    (let* decl = g_declaration_group_of_json A.TraitDeclId.id_of_json js in
     match decl with
     | NonRec id -> Ok id
     | Rec _ -> Error "got mutually dependent trait decls")

let trait_implementation_group_of_json (js : json) :
    (A.TraitImplId.id, string) result =
  combine_error_msgs js __FUNCTION__
    (let* decl = g_declaration_group_of_json A.TraitImplId.id_of_json js in
     match decl with
     | NonRec id -> Ok id
     | Rec _ -> Error "got mutually dependent trait impls")

let declaration_group_of_json (js : json) : (A.declaration_group, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Type", decl) ] ->
        let* decl = type_declaration_group_of_json decl in
        Ok (A.Type decl)
    | `Assoc [ ("Fun", decl) ] ->
        let* decl = fun_declaration_group_of_json decl in
        Ok (A.Fun decl)
    | `Assoc [ ("Global", decl) ] ->
        let* id = global_declaration_group_of_json decl in
        Ok (A.Global id)
    | `Assoc [ ("TraitDecl", decl) ] ->
        let* id = trait_declaration_group_of_json decl in
        Ok (A.TraitDecl id)
    | `Assoc [ ("TraitImpl", decl) ] ->
        let* id = trait_implementation_group_of_json decl in
        Ok (A.TraitImpl id)
    | _ -> Error "")

let length_of_json_list (js : json) : (int, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List jsl -> Ok (List.length jsl)
    | _ -> Error ("not a list: " ^ show js))
