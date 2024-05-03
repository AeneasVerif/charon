(** Functions to load (U)LLBC ASTs from json.

    Initially, we used [ppx_derive_yojson] to automate this.
    However, [ppx_derive_yojson] expects formatting to be slightly
    different from what [serde_rs] generates (because it uses [Yojson.Safe.t]
    and not [Yojson.Basic.t]).

    TODO: we should check all that the integer values are in the proper range
 *)

open Yojson.Basic
open OfJsonBasic
open Identifiers
open Meta
open Values
open Types
open Scalars
open Expressions
open GAst
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

let inline_attr_of_json (js : json) : (inline_attr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Hint" -> Ok Hint
    | `String "Never" -> Ok Never
    | `String "Always" -> Ok Always
    | _ -> Error "")

let item_meta_of_json (id_to_file : id_to_file_map) (js : json) :
    (item_meta, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("meta", meta);
          ("attributes", attributes);
          ("inline", inline);
          ("public", public);
        ] ->
        let* meta = meta_of_json id_to_file meta in
        let* attributes = list_of_json string_of_json attributes in
        let* inline = option_of_json inline_attr_of_json inline in
        let* public = bool_of_json public in
        Ok { meta; attributes; inline; public }
    | _ -> Error "")

let type_var_of_json (js : json) : (type_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = TypeVarId.id_of_json index in
        let* name = string_of_json name in
        Ok { index; name }
    | _ -> Error "")

let region_var_of_json (js : json) : (region_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = RegionVarId.id_of_json index in
        let* name = string_option_of_json name in
        Ok { index; name }
    | _ -> Error "")

let region_of_json (js : json) : (region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Static" -> Ok RStatic
    | `String "Erased" -> Ok RErased
    | `Assoc [ ("BVar", `List [ dbid; rid ]) ] ->
        let* dbid = int_of_json dbid in
        let* rid = RegionVarId.id_of_json rid in
        Ok (RBVar (dbid, rid) : region)
    | _ -> Error "")

let integer_type_of_json (js : json) : (integer_type, string) result =
  match js with
  | `String "Isize" -> Ok Isize
  | `String "I8" -> Ok I8
  | `String "I16" -> Ok I16
  | `String "I32" -> Ok I32
  | `String "I64" -> Ok I64
  | `String "I128" -> Ok I128
  | `String "Usize" -> Ok Usize
  | `String "U8" -> Ok U8
  | `String "U16" -> Ok U16
  | `String "U32" -> Ok U32
  | `String "U64" -> Ok U64
  | `String "U128" -> Ok U128
  | _ -> Error ("integer_type_of_json failed on: " ^ show js)

let literal_type_of_json (js : json) : (literal_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Integer", int_ty) ] ->
        let* int_ty = integer_type_of_json int_ty in
        Ok (TInteger int_ty)
    | `String "Bool" -> Ok TBool
    | `String "Char" -> Ok TChar
    | _ -> Error "")

let const_generic_var_of_json (js : json) : (const_generic_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = ConstGenericVarId.id_of_json index in
        let* name = string_of_json name in
        let* ty = literal_type_of_json ty in
        Ok { index; name; ty }
    | _ -> Error "")

let ref_kind_of_json (js : json) : (ref_kind, string) result =
  match js with
  | `String "Mut" -> Ok RMut
  | `String "Shared" -> Ok RShared
  | _ -> Error ("ref_kind_of_json failed on: " ^ show js)

let assumed_ty_of_json (js : json) : (assumed_ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Box" -> Ok TBox
    | `String "Array" -> Ok TArray
    | `String "Slice" -> Ok TSlice
    | `String "Str" -> Ok TStr
    | _ -> Error "")

let type_id_of_json (js : json) : (type_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", id) ] ->
        let* id = TypeDeclId.id_of_json id in
        Ok (TAdtId id)
    | `String "Tuple" -> Ok TTuple
    | `Assoc [ ("Assumed", aty) ] ->
        let* aty = assumed_ty_of_json aty in
        Ok (TAssumed aty)
    | _ -> Error "")

let big_int_of_json (js : json) : (big_int, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Int i -> Ok (Z.of_int i)
    | `String is -> Ok (Z.of_string is)
    | _ -> Error "")

(** Deserialize a {!Values.scalar_value} from JSON and **check the ranges**.

    Note that in practice we also check that the values are in range
    in the interpreter functions. Still, it doesn't cost much to be
    a bit conservative.
 *)
let scalar_value_of_json (js : json) : (scalar_value, string) result =
  let res =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("Isize", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = Isize }
      | `Assoc [ ("I8", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = I8 }
      | `Assoc [ ("I16", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = I16 }
      | `Assoc [ ("I32", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = I32 }
      | `Assoc [ ("I64", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = I64 }
      | `Assoc [ ("I128", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = I128 }
      | `Assoc [ ("Usize", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = Usize }
      | `Assoc [ ("U8", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = U8 }
      | `Assoc [ ("U16", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = U16 }
      | `Assoc [ ("U32", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = U32 }
      | `Assoc [ ("U64", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = U64 }
      | `Assoc [ ("U128", bi) ] ->
          let* bi = big_int_of_json bi in
          Ok { value = bi; int_ty = U128 }
      | _ -> Error "")
  in
  match res with
  | Error _ -> res
  | Ok sv ->
      if not (check_scalar_value_in_range sv) then (
        log#serror ("Scalar value not in range: " ^ show_scalar_value sv);
        raise (Failure ("Scalar value not in range: " ^ show_scalar_value sv)));
      res

let literal_of_json (js : json) : (literal, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", v) ] ->
        let* v = scalar_value_of_json v in
        Ok (VScalar v)
    | `Assoc [ ("Bool", v) ] ->
        let* v = bool_of_json v in
        Ok (VBool v)
    | `Assoc [ ("Char", v) ] ->
        let* v = char_of_json v in
        Ok (VChar v)
    | _ -> Error "")

let const_generic_of_json (js : json) : (const_generic, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Global", id) ] ->
        let* id = GlobalDeclId.id_of_json id in
        Ok (CgGlobal id)
    | `Assoc [ ("Var", id) ] ->
        let* id = ConstGenericVarId.id_of_json id in
        Ok (CgVar id)
    | `Assoc [ ("Value", lit) ] ->
        let* lit = literal_of_json lit in
        Ok (CgValue lit)
    | _ -> Error "")

let rec ty_of_json (js : json) : (ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ id; generics ]) ] ->
        let* id = type_id_of_json id in
        let* generics = generic_args_of_json generics in
        (* Sanity check *)
        (match id with
        | TTuple -> assert (generics.regions = [] && generics.trait_refs = [])
        | _ -> ());
        Ok (TAdt (id, generics))
    | `Assoc [ ("TypeVar", id) ] ->
        let* id = TypeVarId.id_of_json id in
        Ok (TVar id)
    | `Assoc [ ("Literal", ty) ] ->
        let* ty = literal_type_of_json ty in
        Ok (TLiteral ty)
    | `Assoc [ ("Ref", `List [ region; ty; ref_kind ]) ] ->
        let* region = region_of_json region in
        let* ty = ty_of_json ty in
        let* ref_kind = ref_kind_of_json ref_kind in
        Ok (TRef (region, ty, ref_kind))
    | `Assoc [ ("RawPtr", `List [ ty; ref_kind ]) ] ->
        let* ty = ty_of_json ty in
        let* ref_kind = ref_kind_of_json ref_kind in
        Ok (TRawPtr (ty, ref_kind))
    | `Assoc [ ("TraitType", `List [ trait_ref; item_name ]) ] ->
        let* trait_ref = trait_ref_of_json trait_ref in
        let* item_name = string_of_json item_name in
        Ok (TTraitType (trait_ref, item_name))
    | `Assoc [ ("Arrow", `List [ regions; inputs; output ]) ] ->
        let* regions = list_of_json region_var_of_json regions in
        let* inputs = list_of_json ty_of_json inputs in
        let* output = ty_of_json output in
        Ok (TArrow (regions, inputs, output))
    | _ -> Error "")

and trait_ref_of_json (js : json) : (trait_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("trait_id", trait_id);
          ("generics", generics);
          ("trait_decl_ref", trait_decl_ref);
        ] ->
        let* trait_id = trait_instance_id_of_json trait_id in
        let* generics = generic_args_of_json generics in
        let* trait_decl_ref = trait_decl_ref_of_json trait_decl_ref in
        Ok ({ trait_id; generics; trait_decl_ref } : trait_ref)
    | _ -> Error "")

and trait_decl_ref_of_json (js : json) : (trait_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("trait_id", trait_id); ("generics", generics) ] ->
        let* trait_decl_id = TraitDeclId.id_of_json trait_id in
        let* decl_generics = generic_args_of_json generics in
        Ok ({ trait_decl_id; decl_generics } : trait_decl_ref)
    | _ -> Error "")

and generic_args_of_json (js : json) : (generic_args, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("regions", regions);
          ("types", types);
          ("const_generics", const_generics);
          ("trait_refs", trait_refs);
        ] ->
        let* regions = list_of_json region_of_json regions in
        let* types = list_of_json ty_of_json types in
        let* const_generics =
          list_of_json const_generic_of_json const_generics
        in
        let* trait_refs = list_of_json trait_ref_of_json trait_refs in
        Ok { regions; types; const_generics; trait_refs }
    | _ -> Error "")

and trait_instance_id_of_json (js : json) : (trait_instance_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "SelfId" -> Ok Self
    | `Assoc [ ("TraitImpl", id) ] ->
        let* id = TraitImplId.id_of_json id in
        Ok (TraitImpl id)
    | `Assoc [ ("BuiltinOrAuto", id) ] ->
        let* id = TraitDeclId.id_of_json id in
        Ok (BuiltinOrAuto id)
    | `Assoc [ ("Clause", id) ] ->
        let* id = TraitClauseId.id_of_json id in
        Ok (Clause id)
    | `Assoc [ ("ParentClause", `List [ inst_id; decl_id; clause_id ]) ] ->
        let* inst_id = trait_instance_id_of_json inst_id in
        let* decl_id = TraitDeclId.id_of_json decl_id in
        let* clause_id = TraitClauseId.id_of_json clause_id in
        Ok (ParentClause (inst_id, decl_id, clause_id))
    | `Assoc
        [ ("ItemClause", `List [ inst_id; decl_id; item_name; clause_id ]) ] ->
        let* inst_id = trait_instance_id_of_json inst_id in
        let* decl_id = TraitDeclId.id_of_json decl_id in
        let* item_name = string_of_json item_name in
        let* clause_id = TraitClauseId.id_of_json clause_id in
        Ok (ItemClause (inst_id, decl_id, item_name, clause_id))
    | `Assoc [ ("FnPointer", ty) ] ->
        let* ty = ty_of_json ty in
        Ok (FnPointer ty)
    | `Assoc [ ("Closure", `List [ fid; generics ]) ] ->
        let* fid = FunDeclId.id_of_json fid in
        let* generics = generic_args_of_json generics in
        Ok (Closure (fid, generics))
    | _ -> Error "")

let field_of_json (id_to_file : id_to_file_map) (js : json) :
    (field, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("name", name); ("ty", ty) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* name = option_of_json string_of_json name in
        let* ty = ty_of_json ty in
        Ok { meta; field_name = name; field_ty = ty }
    | _ -> Error "")

let variant_of_json (id_to_file : id_to_file_map) (js : json) :
    (variant, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("meta", meta);
          ("name", name);
          ("fields", fields);
          ("discriminant", discriminant);
        ] ->
        let* meta = meta_of_json id_to_file meta in
        let* name = string_of_json name in
        let* fields = list_of_json (field_of_json id_to_file) fields in
        let* discriminant = scalar_value_of_json discriminant in
        Ok { meta; variant_name = name; fields; discriminant }
    | _ -> Error "")

let type_decl_kind_of_json (id_to_file : id_to_file_map) (js : json) :
    (type_decl_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Struct", fields) ] ->
        let* fields = list_of_json (field_of_json id_to_file) fields in
        Ok (Struct fields)
    | `Assoc [ ("Enum", variants) ] ->
        let* variants = list_of_json (variant_of_json id_to_file) variants in
        Ok (Enum variants)
    | `String "Opaque" -> Ok Opaque
    | _ -> Error "")

let region_var_group_of_json (js : json) : (region_var_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("regions", regions); ("parents", parents) ] ->
        let* id = RegionGroupId.id_of_json id in
        let* regions = list_of_json RegionVarId.id_of_json regions in
        let* parents = list_of_json RegionGroupId.id_of_json parents in
        Ok { id; regions; parents }
    | _ -> Error "")

let region_var_groups_of_json (js : json) : (region_var_groups, string) result =
  combine_error_msgs js __FUNCTION__ (list_of_json region_var_group_of_json js)

let trait_clause_of_json (id_to_file : id_to_file_map) (js : json) :
    (trait_clause, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("clause_id", clause_id);
          ("meta", meta);
          ("trait_id", trait_id);
          ("generics", generics);
        ] ->
        let* clause_id = TraitClauseId.id_of_json clause_id in
        let* meta = option_of_json (meta_of_json id_to_file) meta in
        let* trait_id = TraitDeclId.id_of_json trait_id in
        let* clause_generics = generic_args_of_json generics in
        Ok ({ clause_id; meta; trait_id; clause_generics } : trait_clause)
    | _ -> Error "")

let generic_params_of_json (id_to_file : id_to_file_map) (js : json) :
    (generic_params, string) result =
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
        Ok { regions; types; const_generics; trait_clauses }
    | _ -> Error "")

let region_outlives_of_json (js : json) : (region_outlives, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List [ r0; r1 ] ->
        let* r0 = region_of_json r0 in
        let* r1 = region_of_json r1 in
        Ok (r0, r1)
    | _ -> Error "")

let type_outlives_of_json (js : json) : (type_outlives, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List [ ty; r ] ->
        let* ty = ty_of_json ty in
        let* r = region_of_json r in
        Ok (ty, r)
    | _ -> Error "")

let trait_type_constraint_of_json (js : json) :
    (trait_type_constraint, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("trait_ref", trait_ref); ("type_name", type_name); ("ty", ty) ]
      ->
        let* trait_ref = trait_ref_of_json trait_ref in
        let* type_name = string_of_json type_name in
        let* ty = ty_of_json ty in
        Ok ({ trait_ref; type_name; ty } : trait_type_constraint)
    | _ -> Error "")

let predicates_of_json (js : json) : (predicates, string) result =
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
          list_of_json trait_type_constraint_of_json trait_type_constraints
        in
        Ok { regions_outlive; types_outlive; trait_type_constraints }
    | _ -> Error "")

let impl_elem_kind_of_json (js : json) : (impl_elem_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ty", ty) ] ->
        let* ty = ty_of_json ty in
        Ok (ImplElemTy ty)
    | `Assoc [ ("Trait", tr) ] ->
        let* tr = trait_decl_ref_of_json tr in
        Ok (ImplElemTrait tr)
    | _ -> Error "")

let impl_elem_of_json (id_to_file : id_to_file_map) (js : json) :
    (impl_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("disambiguator", disambiguator);
          ("generics", generics);
          ("preds", preds);
          ("kind", kind);
        ] ->
        let* disambiguator = Disambiguator.id_of_json disambiguator in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* kind = impl_elem_kind_of_json kind in
        Ok { disambiguator; generics; preds; kind }
    | _ -> Error "")

let path_elem_of_json (id_to_file : id_to_file_map) (js : json) :
    (path_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ident", `List [ name; d ]) ] ->
        let* name = string_of_json name in
        let* d = Disambiguator.id_of_json d in
        Ok (PeIdent (name, d))
    | `Assoc [ ("Impl", impl) ] ->
        let* d = impl_elem_of_json id_to_file impl in
        Ok (PeImpl d)
    | _ -> Error "")

let name_of_json (id_to_file : id_to_file_map) (js : json) :
    (name, string) result =
  combine_error_msgs js __FUNCTION__
    (list_of_json (path_elem_of_json id_to_file) js)

let type_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (type_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("is_local", is_local);
          ("name", name);
          ("generics", generics);
          ("preds", preds);
          ("kind", kind);
        ] ->
        let* def_id = TypeDeclId.id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* is_local = bool_of_json is_local in
        let* name = name_of_json id_to_file name in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* kind = type_decl_kind_of_json id_to_file kind in
        Ok { def_id; item_meta; is_local; name; generics; preds; kind }
    | _ -> Error "")

let var_of_json (js : json) : (var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = VarId.id_of_json index in
        let* name = string_option_of_json name in
        let* var_ty = ty_of_json ty in
        Ok { index; name; var_ty }
    | _ -> Error "")

let field_proj_kind_of_json (js : json) : (field_proj_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("ProjAdt", `List [ def_id; opt_variant_id ]) ] ->
        let* def_id = TypeDeclId.id_of_json def_id in
        let* opt_variant_id =
          option_of_json VariantId.id_of_json opt_variant_id
        in
        Ok (ProjAdt (def_id, opt_variant_id))
    | `Assoc [ ("ProjTuple", i) ] ->
        let* i = int_of_json i in
        Ok (ProjTuple i)
    | _ -> Error "")

let projection_elem_of_json (js : json) : (projection_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Deref" -> Ok Deref
    | `String "DerefBox" -> Ok DerefBox
    | `Assoc [ ("Field", `List [ proj_kind; field_id ]) ] ->
        let* proj_kind = field_proj_kind_of_json proj_kind in
        let* field_id = FieldId.id_of_json field_id in
        Ok (Field (proj_kind, field_id))
    | _ -> Error ("projection_elem_of_json failed on:" ^ show js))

let projection_of_json (js : json) : (projection, string) result =
  combine_error_msgs js __FUNCTION__ (list_of_json projection_elem_of_json js)

let place_of_json (js : json) : (place, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("var_id", var_id); ("projection", projection) ] ->
        let* var_id = VarId.id_of_json var_id in
        let* projection = projection_of_json projection in
        Ok { var_id; projection }
    | _ -> Error "")

let borrow_kind_of_json (js : json) : (borrow_kind, string) result =
  match js with
  | `String "Shared" -> Ok BShared
  | `String "Mut" -> Ok BMut
  | `String "TwoPhaseMut" -> Ok BTwoPhaseMut
  | `String "Shallow" -> Ok BShallow
  | _ -> Error ("borrow_kind_of_json failed on:" ^ show js)

let cast_kind_of_json (js : json) : (cast_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", `List [ src_ty; tgt_ty ]) ] ->
        let* src_ty = literal_type_of_json src_ty in
        let* tgt_ty = literal_type_of_json tgt_ty in
        Ok (CastScalar (src_ty, tgt_ty))
    | `Assoc [ ("FnPtr", `List [ src_ty; tgt_ty ]) ] ->
        let* src_ty = ty_of_json src_ty in
        let* tgt_ty = ty_of_json tgt_ty in
        Ok (CastFnPtr (src_ty, tgt_ty))
    | _ -> Error "")

let unop_of_json (js : json) : (unop, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Not" -> Ok Not
    | `String "Neg" -> Ok Neg
    | `Assoc [ ("Cast", cast_kind) ] ->
        let* cast_kind = cast_kind_of_json cast_kind in
        Ok (Cast cast_kind)
    | _ -> Error "")

let binop_of_json (js : json) : (binop, string) result =
  match js with
  | `String "BitXor" -> Ok BitXor
  | `String "BitAnd" -> Ok BitAnd
  | `String "BitOr" -> Ok BitOr
  | `String "Eq" -> Ok Eq
  | `String "Lt" -> Ok Lt
  | `String "Le" -> Ok Le
  | `String "Ne" -> Ok Ne
  | `String "Ge" -> Ok Ge
  | `String "Gt" -> Ok Gt
  | `String "Div" -> Ok Div
  | `String "Rem" -> Ok Rem
  | `String "Add" -> Ok Add
  | `String "Sub" -> Ok Sub
  | `String "Mul" -> Ok Mul
  | `String "Shl" -> Ok Shl
  | `String "Shr" -> Ok Shr
  | _ -> Error ("binop_of_json failed on:" ^ show js)

let literal_of_json (js : json) : (literal, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", scalar_value) ] ->
        let* scalar_value = scalar_value_of_json scalar_value in
        Ok (VScalar scalar_value)
    | `Assoc [ ("Bool", v) ] ->
        let* v = bool_of_json v in
        Ok (VBool v)
    | `Assoc [ ("Char", v) ] ->
        let* v = char_of_json v in
        Ok (VChar v)
    | _ -> Error "")

let assumed_fun_id_of_json (js : json) : (assumed_fun_id, string) result =
  match js with
  | `String "BoxNew" -> Ok BoxNew
  | `String "BoxFree" -> Ok BoxFree
  | `String "ArrayIndexShared" -> Ok ArrayIndexShared
  | `String "ArrayIndexMut" -> Ok ArrayIndexMut
  | `String "ArrayToSliceShared" -> Ok ArrayToSliceShared
  | `String "ArrayToSliceMut" -> Ok ArrayToSliceMut
  | `String "ArrayRepeat" -> Ok ArrayRepeat
  | `String "SliceIndexShared" -> Ok SliceIndexShared
  | `String "SliceIndexMut" -> Ok SliceIndexMut
  | _ -> Error ("assumed_fun_id_of_json failed on:" ^ show js)

let fun_id_of_json (js : json) : (fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", id) ] ->
        let* id = FunDeclId.id_of_json id in
        Ok (FRegular id)
    | `Assoc [ ("Assumed", fid) ] ->
        let* fid = assumed_fun_id_of_json fid in
        Ok (FAssumed fid)
    | _ -> Error "")

let fun_id_or_trait_method_ref_of_json (js : json) :
    (fun_id_or_trait_method_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Fun", id) ] ->
        let* id = fun_id_of_json id in
        Ok (FunId id)
    | `Assoc [ ("Trait", `List [ trait_ref; method_name; fun_decl_id ]) ] ->
        let* trait_ref = trait_ref_of_json trait_ref in
        let* method_name = string_of_json method_name in
        let* fun_decl_id = FunDeclId.id_of_json fun_decl_id in
        Ok (TraitMethod (trait_ref, method_name, fun_decl_id))
    | _ -> Error "")

let fn_ptr_of_json (js : json) : (fn_ptr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("func", func); ("generics", generics) ] ->
        let* func = fun_id_or_trait_method_ref_of_json func in
        let* generics = generic_args_of_json generics in
        Ok { func; generics }
    | _ -> Error "")

let fn_operand_of_json (js : json) : (fn_operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", func) ] ->
        let* func = fn_ptr_of_json func in
        Ok (FnOpRegular func)
    | `Assoc [ ("Move", p) ] ->
        let* p = place_of_json p in
        Ok (FnOpMove p)
    | _ -> Error "")

let rec constant_expr_of_json (js : json) : (constant_expr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("value", value); ("ty", ty) ] ->
        let* value = raw_constant_expr_of_json value in
        let* ty = ty_of_json ty in
        Ok { value; ty }
    | _ -> Error "")

and raw_constant_expr_of_json (js : json) : (raw_constant_expr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Literal", lit) ] ->
        let* lit = literal_of_json lit in
        Ok (CLiteral lit)
    | `Assoc [ ("Var", vid) ] ->
        let* vid = ConstGenericVarId.id_of_json vid in
        Ok (CVar vid)
    | `Assoc [ ("TraitConst", `List [ trait_ref; const_name ]) ] ->
        let* trait_ref = trait_ref_of_json trait_ref in
        let* const_name = string_of_json const_name in
        Ok (CTraitConst (trait_ref, const_name))
    | `Assoc [ ("FnPtr", fn_ptr) ] ->
        let* fn_ptr = fn_ptr_of_json fn_ptr in
        Ok (CFnPtr fn_ptr)
    | _ -> Error "")

let operand_of_json (js : json) : (operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Copy", place) ] ->
        let* place = place_of_json place in
        Ok (Copy place)
    | `Assoc [ ("Move", place) ] ->
        let* place = place_of_json place in
        Ok (Move place)
    | `Assoc [ ("Const", cv) ] ->
        let* cv = constant_expr_of_json cv in
        Ok (Constant cv)
    | _ -> Error "")

let aggregate_kind_of_json (js : json) : (aggregate_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ id; opt_variant_id; generics ]) ] ->
        let* id = type_id_of_json id in
        let* opt_variant_id =
          option_of_json VariantId.id_of_json opt_variant_id
        in
        let* generics = generic_args_of_json generics in
        Ok (AggregatedAdt (id, opt_variant_id, generics))
    | `Assoc [ ("Array", `List [ ty; cg ]) ] ->
        let* ty = ty_of_json ty in
        let* cg = const_generic_of_json cg in
        Ok (AggregatedArray (ty, cg))
    | `Assoc [ ("Closure", `List [ fid; generics ]) ] ->
        let* fid = FunDeclId.id_of_json fid in
        let* generics = generic_args_of_json generics in
        Ok (AggregatedClosure (fid, generics))
    | _ -> Error "")

let rvalue_of_json (js : json) : (rvalue, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Use", op) ] ->
        let* op = operand_of_json op in
        Ok (Use op)
    | `Assoc [ ("Ref", `List [ place; borrow_kind ]) ] ->
        let* place = place_of_json place in
        let* borrow_kind = borrow_kind_of_json borrow_kind in
        Ok (RvRef (place, borrow_kind))
    | `Assoc [ ("UnaryOp", `List [ unop; op ]) ] ->
        let* unop = unop_of_json unop in
        let* op = operand_of_json op in
        Ok (UnaryOp (unop, op))
    | `Assoc [ ("BinaryOp", `List [ binop; op1; op2 ]) ] ->
        let* binop = binop_of_json binop in
        let* op1 = operand_of_json op1 in
        let* op2 = operand_of_json op2 in
        Ok (BinaryOp (binop, op1, op2))
    | `Assoc [ ("Discriminant", `List [ place; adt_id ]) ] ->
        let* place = place_of_json place in
        let* adt_id = TypeDeclId.id_of_json adt_id in
        Ok (Discriminant (place, adt_id))
    | `Assoc [ ("Global", `List [ gid; generics ]) ] ->
        let* gid = GlobalDeclId.id_of_json gid in
        let* generics = generic_args_of_json generics in
        Ok (Global (gid, generics) : rvalue)
    | `Assoc [ ("Aggregate", `List [ aggregate_kind; ops ]) ] ->
        let* aggregate_kind = aggregate_kind_of_json aggregate_kind in
        let* ops = list_of_json operand_of_json ops in
        Ok (Aggregate (aggregate_kind, ops))
    | _ -> Error "")

let params_info_of_json (js : json) : (params_info, string) result =
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
            num_region_params;
            num_type_params;
            num_const_generic_params;
            num_trait_clauses;
            num_regions_outlive;
            num_types_outlive;
            num_trait_type_constraints;
          }
    | _ -> Error "")

let closure_kind_of_json (js : json) : (closure_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Fn" -> Ok Fn
    | `String "FnMut" -> Ok FnMut
    | `String "FnOnce" -> Ok FnOnce
    | _ -> Error "")

let closure_info_of_json (js : json) : (closure_info, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("kind", kind); ("state", state) ] ->
        let* kind = closure_kind_of_json kind in
        let* state = list_of_json ty_of_json state in
        Ok { kind; state }
    | _ -> Error "")

let fun_sig_of_json (id_to_file : id_to_file_map) (js : json) :
    (fun_sig, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("is_unsafe", is_unsafe);
          ("is_closure", is_closure);
          ("closure_info", closure_info);
          ("generics", generics);
          ("preds", preds);
          ("parent_params_info", parent_params_info);
          ("inputs", inputs);
          ("output", output);
        ] ->
        let* is_unsafe = bool_of_json is_unsafe in
        let* is_closure = bool_of_json is_closure in
        let* closure_info = option_of_json closure_info_of_json closure_info in

        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* parent_params_info =
          option_of_json params_info_of_json parent_params_info
        in
        let* inputs = list_of_json ty_of_json inputs in
        let* output = ty_of_json output in
        Ok
          {
            is_unsafe;
            is_closure;
            closure_info;
            generics;
            preds;
            parent_params_info;
            inputs;
            output;
          }
    | _ -> Error "")

let call_of_json (js : json) : (call, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("func", func); ("args", args); ("dest", dest) ] ->
        let* func = fn_operand_of_json func in
        let* args = list_of_json operand_of_json args in
        let* dest = place_of_json dest in
        Ok { func; args; dest }
    | _ -> Error "")

let gexpr_body_of_json (body_of_json : json -> ('body, string) result)
    (id_to_file : id_to_file_map) (js : json) :
    ('body gexpr_body, string) result =
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
        Ok { meta; arg_count; locals; body }
    | _ -> Error "")

let item_kind_of_json (js : json) : (item_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Regular" -> Ok RegularKind
    | `Assoc
        [
          ( "TraitItemImpl",
            `Assoc
              [
                ("impl_id", impl_id);
                ("trait_id", trait_id);
                ("item_name", method_name);
                ("provided", provided);
              ] );
        ] ->
        let* impl_id = TraitImplId.id_of_json impl_id in
        let* trait_id = TraitDeclId.id_of_json trait_id in
        let* method_name = string_of_json method_name in
        let* provided = bool_of_json provided in
        Ok (TraitItemImpl (impl_id, trait_id, method_name, provided))
    | `Assoc [ ("TraitItemDecl", `List [ trait_id; item_name ]) ] ->
        let* trait_id = TraitDeclId.id_of_json trait_id in
        let* item_name = string_of_json item_name in
        Ok (TraitItemDecl (trait_id, item_name))
    | `Assoc [ ("TraitItemProvided", `List [ trait_id; item_name ]) ] ->
        let* trait_id = TraitDeclId.id_of_json trait_id in
        let* item_name = string_of_json item_name in
        Ok (TraitItemProvided (trait_id, item_name))
    | _ -> Error "")

let gfun_decl_of_json (body_of_json : json -> ('body, string) result)
    (id_to_file : id_to_file_map) (js : json) : ('body gfun_decl, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("is_local", is_local);
          ("name", name);
          ("signature", signature);
          ("kind", kind);
          ("body", body);
        ] ->
        let* def_id = FunDeclId.id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* is_local = bool_of_json is_local in
        let* name = name_of_json id_to_file name in
        let* signature = fun_sig_of_json id_to_file signature in
        let* kind = item_kind_of_json kind in
        let* body =
          option_of_json (gexpr_body_of_json body_of_json id_to_file) body
        in
        Ok
          {
            def_id;
            item_meta;
            is_local;
            name;
            signature;
            kind;
            body;
            is_global_decl_body = false;
          }
    | _ -> Error "")

let gglobal_decl_of_json (body_of_json : json -> ('body, string) result)
    (id_to_file : id_to_file_map) (js : json) :
    ('body gexpr_body option gglobal_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("is_local", is_local);
          ("name", name);
          ("generics", generics);
          ("preds", preds);
          ("ty", ty);
          ("kind", kind);
          ("body", body);
        ] ->
        let* global_id = GlobalDeclId.id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* is_local = bool_of_json is_local in
        let* name = name_of_json id_to_file name in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* ty = ty_of_json ty in
        let* body =
          option_of_json (gexpr_body_of_json body_of_json id_to_file) body
        in
        let* kind = item_kind_of_json kind in
        let global =
          {
            def_id = global_id;
            item_meta;
            is_local;
            name;
            body;
            generics;
            preds;
            ty;
            kind;
          }
        in
        Ok global
    | _ -> Error "")

let trait_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (trait_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("is_local", is_local);
          ("item_meta", item_meta);
          ("name", name);
          ("generics", generics);
          ("preds", preds);
          ("parent_clauses", parent_clauses);
          ("consts", consts);
          ("types", types);
          ("required_methods", required_methods);
          ("provided_methods", provided_methods);
        ] ->
        let* def_id = TraitDeclId.id_of_json def_id in
        let* is_local = bool_of_json is_local in
        let* name = name_of_json id_to_file name in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* parent_clauses =
          list_of_json (trait_clause_of_json id_to_file) parent_clauses
        in
        let* consts =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json ty_of_json
                  (option_of_json GlobalDeclId.id_of_json)))
            consts
        in
        let* types =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json
                  (list_of_json (trait_clause_of_json id_to_file))
                  (option_of_json ty_of_json)))
            types
        in
        let* required_methods =
          list_of_json
            (pair_of_json string_of_json FunDeclId.id_of_json)
            required_methods
        in
        let* provided_methods =
          list_of_json
            (pair_of_json string_of_json (option_of_json FunDeclId.id_of_json))
            provided_methods
        in
        Ok
          {
            def_id;
            item_meta;
            is_local;
            name;
            generics;
            preds;
            parent_clauses;
            consts;
            types;
            required_methods;
            provided_methods;
          }
    | _ -> Error "")

let trait_impl_of_json (id_to_file : id_to_file_map) (js : json) :
    (trait_impl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("is_local", is_local);
          ("name", name);
          ("item_meta", item_meta);
          ("impl_trait", impl_trait);
          ("generics", generics);
          ("preds", preds);
          ("parent_trait_refs", parent_trait_refs);
          ("consts", consts);
          ("types", types);
          ("required_methods", required_methods);
          ("provided_methods", provided_methods);
        ] ->
        let* def_id = TraitImplId.id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* is_local = bool_of_json is_local in
        let* name = name_of_json id_to_file name in
        let* impl_trait = trait_decl_ref_of_json impl_trait in
        let* generics = generic_params_of_json id_to_file generics in
        let* preds = predicates_of_json preds in
        let* parent_trait_refs =
          list_of_json trait_ref_of_json parent_trait_refs
        in
        let* consts =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json ty_of_json GlobalDeclId.id_of_json))
            consts
        in
        let* types =
          list_of_json
            (pair_of_json string_of_json
               (pair_of_json (list_of_json trait_ref_of_json) ty_of_json))
            types
        in
        let methods_of_json =
          list_of_json (pair_of_json string_of_json FunDeclId.id_of_json)
        in
        let* required_methods = methods_of_json required_methods in
        let* provided_methods = methods_of_json provided_methods in
        Ok
          ({
             def_id;
             item_meta;
             is_local;
             name;
             impl_trait;
             generics;
             preds;
             parent_trait_refs;
             consts;
             types;
             required_methods;
             provided_methods;
           }
            : trait_impl)
    | _ -> Error "")

let g_declaration_group_of_json (id_of_json : json -> ('id, string) result)
    (js : json) : ('id g_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("NonRec", id) ] ->
        let* id = id_of_json id in
        Ok (NonRecGroup id)
    | `Assoc [ ("Rec", ids) ] ->
        let* ids = list_of_json id_of_json ids in
        Ok (RecGroup ids)
    | _ -> Error "")

let type_declaration_group_of_json (js : json) :
    (type_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (g_declaration_group_of_json TypeDeclId.id_of_json js)

let fun_declaration_group_of_json (js : json) :
    (fun_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (g_declaration_group_of_json FunDeclId.id_of_json js)

let global_declaration_group_of_json (js : json) :
    (GlobalDeclId.id, string) result =
  combine_error_msgs js __FUNCTION__
    (let* decl = g_declaration_group_of_json GlobalDeclId.id_of_json js in
     match decl with
     | NonRecGroup id -> Ok id
     | RecGroup _ -> Error "got mutually dependent globals")

let trait_declaration_group_of_json (js : json) :
    (TraitDeclId.id, string) result =
  combine_error_msgs js __FUNCTION__
    (let* decl = g_declaration_group_of_json TraitDeclId.id_of_json js in
     match decl with
     | NonRecGroup id -> Ok id
     | RecGroup _ -> Error "got mutually dependent trait decls")

let trait_implementation_group_of_json (js : json) :
    (TraitImplId.id, string) result =
  combine_error_msgs js __FUNCTION__
    (let* decl = g_declaration_group_of_json TraitImplId.id_of_json js in
     match decl with
     | NonRecGroup id -> Ok id
     | RecGroup _ -> Error "got mutually dependent trait impls")

let declaration_group_of_json (js : json) : (declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Type", decl) ] ->
        let* decl = type_declaration_group_of_json decl in
        Ok (TypeGroup decl)
    | `Assoc [ ("Fun", decl) ] ->
        let* decl = fun_declaration_group_of_json decl in
        Ok (FunGroup decl)
    | `Assoc [ ("Global", decl) ] ->
        let* id = global_declaration_group_of_json decl in
        Ok (GlobalGroup id)
    | `Assoc [ ("TraitDecl", decl) ] ->
        let* id = trait_declaration_group_of_json decl in
        Ok (TraitDeclGroup id)
    | `Assoc [ ("TraitImpl", decl) ] ->
        let* id = trait_implementation_group_of_json decl in
        Ok (TraitImplGroup id)
    | _ -> Error "")

let length_of_json_list (js : json) : (int, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List jsl -> Ok (List.length jsl)
    | _ -> Error ("not a list: " ^ show js))
