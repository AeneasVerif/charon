(** WARNING: this file is partially auto-generated. Do not edit `GAstOfJson.ml`
    by hand. Edit `GAstOfJson.template.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `GAstOfJson.template.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

(** Functions to load (U)LLBC ASTs from json.

    Initially, we used [ppx_derive_yojson] to automate this.
    However, [ppx_derive_yojson] expects formatting to be slightly
    different from what [serde_rs] generates (because it uses [Yojson.Safe.t]
    and not [Yojson.Basic.t]).
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

let de_bruijn_id_of_json = int_of_json
let path_buf_of_json = string_of_json
let trait_item_name_of_json = string_of_json
let vector_of_json _ = list_of_json
let const_generic_var_id_of_json = ConstGenericVarId.id_of_json
let disambiguator_of_json = Disambiguator.id_of_json
let field_id_of_json = FieldId.id_of_json
let fun_decl_id_of_json = FunDeclId.id_of_json
let global_decl_id_of_json = GlobalDeclId.id_of_json
let local_file_id_of_json = LocalFileId.id_of_json
let region_id_of_json = RegionVarId.id_of_json
let trait_clause_id_of_json = TraitClauseId.id_of_json
let trait_decl_id_of_json = TraitDeclId.id_of_json
let trait_impl_id_of_json = TraitImplId.id_of_json
let type_decl_id_of_json = TypeDeclId.id_of_json
let type_var_id_of_json = TypeVarId.id_of_json
let variant_id_of_json = VariantId.id_of_json
let var_id_of_json = VarId.id_of_json
let virtual_file_id_of_json = VirtualFileId.id_of_json

(* Start of the `and` chain *)
let __ = ()

and file_id_of_json (js : json) : (file_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("LocalId", local_id) ] ->
        let* local_id = local_file_id_of_json local_id in
        Ok (LocalId local_id)
    | `Assoc [ ("VirtualId", virtual_id) ] ->
        let* virtual_id = virtual_file_id_of_json virtual_id in
        Ok (VirtualId virtual_id)
    | _ -> Error "")

and file_name_of_json (js : json) : (file_name, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Virtual", virtual_) ] ->
        let* virtual_ = path_buf_of_json virtual_ in
        Ok (Virtual virtual_)
    | `Assoc [ ("Local", local) ] ->
        let* local = path_buf_of_json local in
        Ok (Local local)
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

and loc_of_json (js : json) : (loc, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("line", line); ("col", col) ] ->
        let* line = int_of_json line in
        let* col = int_of_json col in
        Ok { line; col }
    | _ -> Error "")

(* This is written by hand because it accessed `id_to_file`. *)
let rec raw_span_of_json (id_to_file : id_to_file_map) (js : json) :
    (raw_span, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("file_id", file_id); ("beg", beg_loc); ("end", end_loc) ] ->
        let* file_id = file_id_of_json file_id in
        let file = IdToFile.find file_id id_to_file in
        let* beg_loc = loc_of_json beg_loc in
        let* end_loc = loc_of_json end_loc in
        Ok { file; beg_loc; end_loc }
    | _ -> Error "")

and span_of_json (id_to_file : id_to_file_map) (js : json) :
    (span, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("generated_from_span", generated_from_span) ] ->
        let* span = raw_span_of_json id_to_file span in
        let* generated_from_span =
          option_of_json (raw_span_of_json id_to_file) generated_from_span
        in
        Ok { span; generated_from_span }
    | _ -> Error "")

and inline_attr_of_json (js : json) : (inline_attr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Hint" -> Ok Hint
    | `String "Never" -> Ok Never
    | `String "Always" -> Ok Always
    | _ -> Error "")

and attribute_of_json (js : json) : (attribute, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Opaque" -> Ok AttrOpaque
    | `Assoc [ ("Rename", rename) ] ->
        let* rename = string_of_json rename in
        Ok (AttrRename rename)
    | `Assoc [ ("VariantsPrefix", variants_prefix) ] ->
        let* variants_prefix = string_of_json variants_prefix in
        Ok (AttrVariantsPrefix variants_prefix)
    | `Assoc [ ("VariantsSuffix", variants_suffix) ] ->
        let* variants_suffix = string_of_json variants_suffix in
        Ok (AttrVariantsSuffix variants_suffix)
    | `Assoc [ ("Unknown", unknown) ] ->
        let* unknown = string_of_json unknown in
        Ok (AttrUnknown unknown)
    | _ -> Error "")

and attr_info_of_json (js : json) : (attr_info, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("attributes", attributes);
          ("inline", inline);
          ("rename", rename);
          ("public", public);
        ] ->
        let* attributes = list_of_json attribute_of_json attributes in
        let* inline = option_of_json inline_attr_of_json inline in
        let* rename = option_of_json string_of_json rename in
        let* public = bool_of_json public in
        Ok { attributes; inline; rename; public }
    | _ -> Error "")

and type_var_of_json (js : json) : (type_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = type_var_id_of_json index in
        let* name = string_of_json name in
        Ok { index; name }
    | _ -> Error "")

and region_var_of_json (js : json) : (region_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = region_id_of_json index in
        let* name = option_of_json string_of_json name in
        Ok { index; name }
    | _ -> Error "")

and region_of_json (js : json) : (region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Static" -> Ok RStatic
    | `Assoc [ ("BVar", `List [ x0; x1 ]) ] ->
        let* x0 = de_bruijn_id_of_json x0 in
        let* x1 = region_id_of_json x1 in
        Ok (RBVar (x0, x1))
    | `String "Erased" -> Ok RErased
    | _ -> Error "")

and integer_type_of_json (js : json) : (integer_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
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
    | _ -> Error "")

and literal_type_of_json (js : json) : (literal_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Integer", integer) ] ->
        let* integer = integer_type_of_json integer in
        Ok (TInteger integer)
    | `String "Bool" -> Ok TBool
    | `String "Char" -> Ok TChar
    | _ -> Error "")

and const_generic_var_of_json (js : json) : (const_generic_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = const_generic_var_id_of_json index in
        let* name = string_of_json name in
        let* ty = literal_type_of_json ty in
        Ok { index; name; ty }
    | _ -> Error "")

and ref_kind_of_json (js : json) : (ref_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Mut" -> Ok RMut
    | `String "Shared" -> Ok RShared
    | _ -> Error "")

and assumed_ty_of_json (js : json) : (assumed_ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Box" -> Ok TBox
    | `String "Array" -> Ok TArray
    | `String "Slice" -> Ok TSlice
    | `String "Str" -> Ok TStr
    | _ -> Error "")

and type_id_of_json (js : json) : (type_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", adt) ] ->
        let* adt = type_decl_id_of_json adt in
        Ok (TAdtId adt)
    | `String "Tuple" -> Ok TTuple
    | `Assoc [ ("Assumed", assumed) ] ->
        let* assumed = assumed_ty_of_json assumed in
        Ok (TAssumed assumed)
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

    This is written by hand because it does not match the structure of the
    corresponding rust type. *)
let rec scalar_value_of_json (js : json) : (scalar_value, string) result =
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

and const_generic_of_json (js : json) : (const_generic, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Global", global) ] ->
        let* global = global_decl_id_of_json global in
        Ok (CgGlobal global)
    | `Assoc [ ("Var", var) ] ->
        let* var = const_generic_var_id_of_json var in
        Ok (CgVar var)
    | `Assoc [ ("Value", value) ] ->
        let* value = literal_of_json value in
        Ok (CgValue value)
    | _ -> Error "")

and ty_of_json (js : json) : (ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ x0; x1 ]) ] ->
        let* x0 = type_id_of_json x0 in
        let* x1 = generic_args_of_json x1 in
        Ok (TAdt (x0, x1))
    | `Assoc [ ("TypeVar", type_var) ] ->
        let* type_var = type_var_id_of_json type_var in
        Ok (TVar type_var)
    | `Assoc [ ("Literal", literal) ] ->
        let* literal = literal_type_of_json literal in
        Ok (TLiteral literal)
    | `String "Never" -> Ok TNever
    | `Assoc [ ("Ref", `List [ x0; x1; x2 ]) ] ->
        let* x0 = region_of_json x0 in
        let* x1 = ty_of_json x1 in
        let* x2 = ref_kind_of_json x2 in
        Ok (TRef (x0, x1, x2))
    | `Assoc [ ("RawPtr", `List [ x0; x1 ]) ] ->
        let* x0 = ty_of_json x0 in
        let* x1 = ref_kind_of_json x1 in
        Ok (TRawPtr (x0, x1))
    | `Assoc [ ("TraitType", `List [ x0; x1 ]) ] ->
        let* x0 = trait_ref_of_json x0 in
        let* x1 = trait_item_name_of_json x1 in
        Ok (TTraitType (x0, x1))
    | `Assoc [ ("DynTrait", dyn_trait) ] ->
        let* dyn_trait = existential_predicate_of_json dyn_trait in
        Ok (TDynTrait dyn_trait)
    | `Assoc [ ("Arrow", `List [ x0; x1; x2 ]) ] ->
        let* x0 = vector_of_json region_id_of_json region_var_of_json x0 in
        let* x1 = list_of_json ty_of_json x1 in
        let* x2 = ty_of_json x2 in
        Ok (TArrow (x0, x1, x2))
    | _ -> Error "")

and existential_predicate_of_json (js : json) :
    (existential_predicate, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with `Null -> Ok () | _ -> Error "")

and trait_ref_of_json (js : json) : (trait_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("kind", kind); ("trait_decl_ref", trait_decl_ref) ] ->
        let* trait_id = trait_instance_id_of_json kind in
        let* trait_decl_ref = trait_decl_ref_of_json trait_decl_ref in
        Ok { trait_id; trait_decl_ref }
    | _ -> Error "")

and trait_decl_ref_of_json (js : json) : (trait_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("trait_id", trait_id); ("generics", generics) ] ->
        let* trait_decl_id = trait_decl_id_of_json trait_id in
        let* decl_generics = generic_args_of_json generics in
        Ok { trait_decl_id; decl_generics }
    | _ -> Error "")

and global_decl_ref_of_json (js : json) : (global_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("generics", generics) ] ->
        let* global_id = global_decl_id_of_json id in
        let* global_generics = generic_args_of_json generics in
        Ok { global_id; global_generics }
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
    | `Assoc [ ("TraitImpl", `List [ x0; x1 ]) ] ->
        let* x0 = trait_impl_id_of_json x0 in
        let* x1 = generic_args_of_json x1 in
        Ok (TraitImpl (x0, x1))
    | `Assoc [ ("Clause", clause) ] ->
        let* clause = trait_clause_id_of_json clause in
        Ok (Clause clause)
    | `Assoc [ ("ParentClause", `List [ x0; x1; x2 ]) ] ->
        let* x0 = trait_instance_id_of_json x0 in
        let* x1 = trait_decl_id_of_json x1 in
        let* x2 = trait_clause_id_of_json x2 in
        Ok (ParentClause (x0, x1, x2))
    | `String "SelfId" -> Ok Self
    | `Assoc [ ("BuiltinOrAuto", builtin_or_auto) ] ->
        let* builtin_or_auto = trait_decl_ref_of_json builtin_or_auto in
        Ok (BuiltinOrAuto builtin_or_auto)
    | `Assoc [ ("Dyn", dyn) ] ->
        let* dyn = trait_decl_ref_of_json dyn in
        Ok (Dyn dyn)
    | `Assoc [ ("Unknown", unknown) ] ->
        let* unknown = string_of_json unknown in
        Ok (UnknownTrait unknown)
    | _ -> Error "")

and field_of_json (id_to_file : id_to_file_map) (js : json) :
    (field, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [ ("span", span); ("attr_info", attr_info); ("name", name); ("ty", ty) ]
      ->
        let* span = span_of_json id_to_file span in
        let* attr_info = attr_info_of_json attr_info in
        let* field_name = option_of_json string_of_json name in
        let* field_ty = ty_of_json ty in
        Ok { span; attr_info; field_name; field_ty }
    | _ -> Error "")

and variant_of_json (id_to_file : id_to_file_map) (js : json) :
    (variant, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("span", span);
          ("attr_info", attr_info);
          ("name", name);
          ("fields", fields);
          ("discriminant", discriminant);
        ] ->
        let* span = span_of_json id_to_file span in
        let* attr_info = attr_info_of_json attr_info in
        let* variant_name = string_of_json name in
        let* fields =
          vector_of_json field_id_of_json (field_of_json id_to_file) fields
        in
        let* discriminant = scalar_value_of_json discriminant in
        Ok { span; attr_info; variant_name; fields; discriminant }
    | _ -> Error "")

and type_decl_kind_of_json (id_to_file : id_to_file_map) (js : json) :
    (type_decl_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Struct", struct_) ] ->
        let* struct_ =
          vector_of_json field_id_of_json (field_of_json id_to_file) struct_
        in
        Ok (Struct struct_)
    | `Assoc [ ("Enum", enum) ] ->
        let* enum =
          vector_of_json variant_id_of_json (variant_of_json id_to_file) enum
        in
        Ok (Enum enum)
    | `String "Opaque" -> Ok Opaque
    | `Assoc [ ("Alias", alias) ] ->
        let* alias = ty_of_json alias in
        Ok (Alias alias)
    | _ -> Error "")

(* This is written by hand because the corresponding rust type does not exist. *)
and region_var_group_of_json (js : json) : (region_var_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("regions", regions); ("parents", parents) ] ->
        let* id = RegionGroupId.id_of_json id in
        let* regions = list_of_json RegionVarId.id_of_json regions in
        let* parents = list_of_json RegionGroupId.id_of_json parents in
        Ok { id; regions; parents }
    | _ -> Error "")

and region_var_groups_of_json (js : json) : (region_var_groups, string) result =
  combine_error_msgs js __FUNCTION__ (list_of_json region_var_group_of_json js)

and trait_clause_of_json (id_to_file : id_to_file_map) (js : json) :
    (trait_clause, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("clause_id", clause_id);
          ("span", span);
          ("origin", _);
          ("trait_", trait_);
        ] ->
        let* clause_id = trait_clause_id_of_json clause_id in
        let* span = option_of_json (span_of_json id_to_file) span in
        let* trait = trait_decl_ref_of_json trait_ in
        Ok { clause_id; span; trait }
    | _ -> Error "")

and outlives_pred_of_json :
      'a0 'a1.
      (json -> ('a0, string) result) ->
      (json -> ('a1, string) result) ->
      json ->
      (('a0, 'a1) outlives_pred, string) result =
 fun arg0_of_json arg1_of_json js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List [ x0; x1 ] ->
        let* x0 = arg0_of_json x0 in
        let* x1 = arg1_of_json x1 in
        Ok (x0, x1)
    | _ -> Error "")

and region_outlives_of_json (js : json) : (region_outlives, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> outlives_pred_of_json region_of_json region_of_json x
    | _ -> Error "")

and type_outlives_of_json (js : json) : (type_outlives, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> outlives_pred_of_json ty_of_json region_of_json x
    | _ -> Error "")

and trait_type_constraint_of_json (js : json) :
    (trait_type_constraint, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("trait_ref", trait_ref); ("type_name", type_name); ("ty", ty) ]
      ->
        let* trait_ref = trait_ref_of_json trait_ref in
        let* type_name = trait_item_name_of_json type_name in
        let* ty = ty_of_json ty in
        Ok { trait_ref; type_name; ty }
    | _ -> Error "")

and generic_params_of_json (id_to_file : id_to_file_map) (js : json) :
    (generic_params, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("regions", regions);
          ("types", types);
          ("const_generics", const_generics);
          ("trait_clauses", trait_clauses);
          ("regions_outlive", regions_outlive);
          ("types_outlive", types_outlive);
          ("trait_type_constraints", trait_type_constraints);
        ] ->
        let* regions =
          vector_of_json region_id_of_json region_var_of_json regions
        in
        let* types =
          vector_of_json type_var_id_of_json type_var_of_json types
        in
        let* const_generics =
          vector_of_json const_generic_var_id_of_json const_generic_var_of_json
            const_generics
        in
        let* trait_clauses =
          vector_of_json trait_clause_id_of_json
            (trait_clause_of_json id_to_file)
            trait_clauses
        in
        let* regions_outlive =
          list_of_json
            (outlives_pred_of_json region_of_json region_of_json)
            regions_outlive
        in
        let* types_outlive =
          list_of_json
            (outlives_pred_of_json ty_of_json region_of_json)
            types_outlive
        in
        let* trait_type_constraints =
          list_of_json trait_type_constraint_of_json trait_type_constraints
        in
        Ok
          {
            regions;
            types;
            const_generics;
            trait_clauses;
            regions_outlive;
            types_outlive;
            trait_type_constraints;
          }
    | _ -> Error "")

and impl_elem_kind_of_json (js : json) : (impl_elem_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ty", ty) ] ->
        let* ty = ty_of_json ty in
        Ok (ImplElemTy ty)
    | `Assoc [ ("Trait", trait) ] ->
        let* trait = trait_decl_ref_of_json trait in
        Ok (ImplElemTrait trait)
    | _ -> Error "")

and impl_elem_of_json (id_to_file : id_to_file_map) (js : json) :
    (impl_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("disambiguator", disambiguator);
          ("generics", generics);
          ("kind", kind);
        ] ->
        let* disambiguator = disambiguator_of_json disambiguator in
        let* generics = generic_params_of_json id_to_file generics in
        let* kind = impl_elem_kind_of_json kind in
        Ok { disambiguator; generics; kind }
    | _ -> Error "")

and path_elem_of_json (id_to_file : id_to_file_map) (js : json) :
    (path_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ident", `List [ x0; x1 ]) ] ->
        let* x0 = string_of_json x0 in
        let* x1 = disambiguator_of_json x1 in
        Ok (PeIdent (x0, x1))
    | `Assoc [ ("Impl", impl) ] ->
        let* impl = impl_elem_of_json id_to_file impl in
        Ok (PeImpl impl)
    | _ -> Error "")

and name_of_json (id_to_file : id_to_file_map) (js : json) :
    (name, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> list_of_json (path_elem_of_json id_to_file) x
    | _ -> Error "")

and item_meta_of_json (id_to_file : id_to_file_map) (js : json) :
    (item_meta, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("span", span);
          ("name", name);
          ("attr_info", attr_info);
          ("is_local", is_local);
          ("opacity", _);
        ] ->
        let* span = span_of_json id_to_file span in
        let* name = name_of_json id_to_file name in
        let* attr_info = attr_info_of_json attr_info in
        let* is_local = bool_of_json is_local in
        Ok { span; name; attr_info; is_local }
    | _ -> Error "")

and type_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (type_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("generics", generics);
          ("kind", kind);
        ] ->
        let* def_id = type_decl_id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* generics = generic_params_of_json id_to_file generics in
        let* kind = type_decl_kind_of_json id_to_file kind in
        Ok { def_id; item_meta; generics; kind }
    | _ -> Error "")

and var_of_json (js : json) : (var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = var_id_of_json index in
        let* name = option_of_json string_of_json name in
        let* var_ty = ty_of_json ty in
        Ok { index; name; var_ty }
    | _ -> Error "")

and field_proj_kind_of_json (js : json) : (field_proj_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ x0; x1 ]) ] ->
        let* x0 = type_decl_id_of_json x0 in
        let* x1 = option_of_json variant_id_of_json x1 in
        Ok (ProjAdt (x0, x1))
    | `Assoc [ ("Tuple", tuple) ] ->
        let* tuple = int_of_json tuple in
        Ok (ProjTuple tuple)
    | _ -> Error "")

and projection_elem_of_json (js : json) : (projection_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Deref" -> Ok Deref
    | `String "DerefBox" -> Ok DerefBox
    | `Assoc [ ("Field", `List [ x0; x1 ]) ] ->
        let* x0 = field_proj_kind_of_json x0 in
        let* x1 = field_id_of_json x1 in
        Ok (Field (x0, x1))
    | _ -> Error "")

and projection_of_json (js : json) : (projection, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | x -> list_of_json projection_elem_of_json x
    | _ -> Error "")

and place_of_json (js : json) : (place, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("var_id", var_id); ("projection", projection) ] ->
        let* var_id = var_id_of_json var_id in
        let* projection = list_of_json projection_elem_of_json projection in
        Ok { var_id; projection }
    | _ -> Error "")

and borrow_kind_of_json (js : json) : (borrow_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Shared" -> Ok BShared
    | `String "Mut" -> Ok BMut
    | `String "TwoPhaseMut" -> Ok BTwoPhaseMut
    | `String "Shallow" -> Ok BShallow
    | _ -> Error "")

and cast_kind_of_json (js : json) : (cast_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", `List [ x0; x1 ]) ] ->
        let* x0 = literal_type_of_json x0 in
        let* x1 = literal_type_of_json x1 in
        Ok (CastScalar (x0, x1))
    | `Assoc [ ("FnPtr", `List [ x0; x1 ]) ] ->
        let* x0 = ty_of_json x0 in
        let* x1 = ty_of_json x1 in
        Ok (CastFnPtr (x0, x1))
    | `Assoc [ ("Unsize", `List [ x0; x1 ]) ] ->
        let* x0 = ty_of_json x0 in
        let* x1 = ty_of_json x1 in
        Ok (CastUnsize (x0, x1))
    | _ -> Error "")

and unop_of_json (js : json) : (unop, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Not" -> Ok Not
    | `String "Neg" -> Ok Neg
    | `Assoc [ ("Cast", cast) ] ->
        let* cast = cast_kind_of_json cast in
        Ok (Cast cast)
    | _ -> Error "")

and binop_of_json (js : json) : (binop, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
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
    | `String "CheckedAdd" -> Ok CheckedAdd
    | `String "CheckedSub" -> Ok CheckedSub
    | `String "CheckedMul" -> Ok CheckedMul
    | `String "Shl" -> Ok Shl
    | `String "Shr" -> Ok Shr
    | _ -> Error "")

and literal_of_json (js : json) : (literal, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", scalar) ] ->
        let* scalar = scalar_value_of_json scalar in
        Ok (VScalar scalar)
    | `Assoc [ ("Bool", bool_) ] ->
        let* bool_ = bool_of_json bool_ in
        Ok (VBool bool_)
    | `Assoc [ ("Char", char_) ] ->
        let* char_ = char_of_json char_ in
        Ok (VChar char_)
    | `Assoc [ ("ByteStr", byte_str) ] ->
        let* byte_str = list_of_json int_of_json byte_str in
        Ok (VByteStr byte_str)
    | `Assoc [ ("Str", str) ] ->
        let* str = string_of_json str in
        Ok (VStr str)
    | _ -> Error "")

and assumed_fun_id_of_json (js : json) : (assumed_fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "BoxNew" -> Ok BoxNew
    | `String "BoxFree" -> Ok BoxFree
    | `String "ArrayIndexShared" -> Ok ArrayIndexShared
    | `String "ArrayIndexMut" -> Ok ArrayIndexMut
    | `String "ArrayToSliceShared" -> Ok ArrayToSliceShared
    | `String "ArrayToSliceMut" -> Ok ArrayToSliceMut
    | `String "ArrayRepeat" -> Ok ArrayRepeat
    | `String "SliceIndexShared" -> Ok SliceIndexShared
    | `String "SliceIndexMut" -> Ok SliceIndexMut
    | _ -> Error "")

and fun_id_of_json (js : json) : (fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", regular) ] ->
        let* regular = fun_decl_id_of_json regular in
        Ok (FRegular regular)
    | `Assoc [ ("Assumed", assumed) ] ->
        let* assumed = assumed_fun_id_of_json assumed in
        Ok (FAssumed assumed)
    | _ -> Error "")

and fun_id_or_trait_method_ref_of_json (js : json) :
    (fun_id_or_trait_method_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Fun", fun_) ] ->
        let* fun_ = fun_id_of_json fun_ in
        Ok (FunId fun_)
    | `Assoc [ ("Trait", `List [ x0; x1; x2 ]) ] ->
        let* x0 = trait_ref_of_json x0 in
        let* x1 = trait_item_name_of_json x1 in
        let* x2 = fun_decl_id_of_json x2 in
        Ok (TraitMethod (x0, x1, x2))
    | _ -> Error "")

and fn_ptr_of_json (js : json) : (fn_ptr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("func", func); ("generics", generics) ] ->
        let* func = fun_id_or_trait_method_ref_of_json func in
        let* generics = generic_args_of_json generics in
        Ok { func; generics }
    | _ -> Error "")

and fn_operand_of_json (js : json) : (fn_operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", regular) ] ->
        let* regular = fn_ptr_of_json regular in
        Ok (FnOpRegular regular)
    | `Assoc [ ("Move", move) ] ->
        let* move = place_of_json move in
        Ok (FnOpMove move)
    | _ -> Error "")

and constant_expr_of_json (js : json) : (constant_expr, string) result =
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
    | `Assoc [ ("Literal", literal) ] ->
        let* literal = literal_of_json literal in
        Ok (CLiteral literal)
    | `Assoc [ ("TraitConst", `List [ x0; x1 ]) ] ->
        let* x0 = trait_ref_of_json x0 in
        let* x1 = trait_item_name_of_json x1 in
        Ok (CTraitConst (x0, x1))
    | `Assoc [ ("Var", var) ] ->
        let* var = const_generic_var_id_of_json var in
        Ok (CVar var)
    | `Assoc [ ("FnPtr", fn_ptr) ] ->
        let* fn_ptr = fn_ptr_of_json fn_ptr in
        Ok (CFnPtr fn_ptr)
    | _ -> Error "")

and operand_of_json (js : json) : (operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Copy", copy) ] ->
        let* copy = place_of_json copy in
        Ok (Copy copy)
    | `Assoc [ ("Move", move) ] ->
        let* move = place_of_json move in
        Ok (Move move)
    | `Assoc [ ("Const", const) ] ->
        let* const = constant_expr_of_json const in
        Ok (Constant const)
    | _ -> Error "")

and aggregate_kind_of_json (js : json) : (aggregate_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ x0; x1; x2 ]) ] ->
        let* x0 = type_id_of_json x0 in
        let* x1 = option_of_json variant_id_of_json x1 in
        let* x2 = generic_args_of_json x2 in
        Ok (AggregatedAdt (x0, x1, x2))
    | `Assoc [ ("Array", `List [ x0; x1 ]) ] ->
        let* x0 = ty_of_json x0 in
        let* x1 = const_generic_of_json x1 in
        Ok (AggregatedArray (x0, x1))
    | `Assoc [ ("Closure", `List [ x0; x1 ]) ] ->
        let* x0 = fun_decl_id_of_json x0 in
        let* x1 = generic_args_of_json x1 in
        Ok (AggregatedClosure (x0, x1))
    | _ -> Error "")

and rvalue_of_json (js : json) : (rvalue, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Use", use) ] ->
        let* use = operand_of_json use in
        Ok (Use use)
    | `Assoc [ ("Ref", `List [ x0; x1 ]) ] ->
        let* x0 = place_of_json x0 in
        let* x1 = borrow_kind_of_json x1 in
        Ok (RvRef (x0, x1))
    | `Assoc [ ("UnaryOp", `List [ x0; x1 ]) ] ->
        let* x0 = unop_of_json x0 in
        let* x1 = operand_of_json x1 in
        Ok (UnaryOp (x0, x1))
    | `Assoc [ ("BinaryOp", `List [ x0; x1; x2 ]) ] ->
        let* x0 = binop_of_json x0 in
        let* x1 = operand_of_json x1 in
        let* x2 = operand_of_json x2 in
        Ok (BinaryOp (x0, x1, x2))
    | `Assoc [ ("Discriminant", `List [ x0; x1 ]) ] ->
        let* x0 = place_of_json x0 in
        let* x1 = type_decl_id_of_json x1 in
        Ok (Discriminant (x0, x1))
    | `Assoc [ ("Aggregate", `List [ x0; x1 ]) ] ->
        let* x0 = aggregate_kind_of_json x0 in
        let* x1 = list_of_json operand_of_json x1 in
        Ok (Aggregate (x0, x1))
    | `Assoc [ ("Global", global) ] ->
        let* global = global_decl_ref_of_json global in
        Ok (Global global)
    | `Assoc [ ("Len", `List [ x0; x1; x2 ]) ] ->
        let* x0 = place_of_json x0 in
        let* x1 = ty_of_json x1 in
        let* x2 = option_of_json const_generic_of_json x2 in
        Ok (Len (x0, x1, x2))
    | _ -> Error "")

and params_info_of_json (js : json) : (params_info, string) result =
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

and closure_kind_of_json (js : json) : (closure_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Fn" -> Ok Fn
    | `String "FnMut" -> Ok FnMut
    | `String "FnOnce" -> Ok FnOnce
    | _ -> Error "")

and closure_info_of_json (js : json) : (closure_info, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("kind", kind); ("state", state) ] ->
        let* kind = closure_kind_of_json kind in
        let* state = list_of_json ty_of_json state in
        Ok { kind; state }
    | _ -> Error "")

and fun_sig_of_json (id_to_file : id_to_file_map) (js : json) :
    (fun_sig, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("is_unsafe", is_unsafe);
          ("is_closure", is_closure);
          ("closure_info", closure_info);
          ("generics", generics);
          ("parent_params_info", parent_params_info);
          ("inputs", inputs);
          ("output", output);
        ] ->
        let* is_unsafe = bool_of_json is_unsafe in
        let* is_closure = bool_of_json is_closure in
        let* closure_info = option_of_json closure_info_of_json closure_info in
        let* generics = generic_params_of_json id_to_file generics in
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
            parent_params_info;
            inputs;
            output;
          }
    | _ -> Error "")

and call_of_json (js : json) : (call, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("func", func); ("args", args); ("dest", dest) ] ->
        let* func = fn_operand_of_json func in
        let* args = list_of_json operand_of_json args in
        let* dest = place_of_json dest in
        Ok { func; args; dest }
    | _ -> Error "")

and gexpr_body_of_json :
      'a0.
      (json -> ('a0, string) result) ->
      id_to_file_map ->
      json ->
      ('a0 gexpr_body, string) result =
 fun arg0_of_json id_to_file js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("span", span);
          ("arg_count", arg_count);
          ("locals", locals);
          ("body", body);
        ] ->
        let* span = span_of_json id_to_file span in
        let* arg_count = int_of_json arg_count in
        let* locals = vector_of_json var_id_of_json var_of_json locals in
        let* body = arg0_of_json body in
        Ok { span; arg_count; locals; body }
    | _ -> Error "")

and item_kind_of_json (js : json) : (item_kind, string) result =
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
                ("item_name", item_name);
                ("provided", provided);
              ] );
        ] ->
        let* impl_id = trait_impl_id_of_json impl_id in
        let* trait_id = trait_decl_id_of_json trait_id in
        let* item_name = trait_item_name_of_json item_name in
        let* provided = bool_of_json provided in
        Ok (TraitItemImpl (impl_id, trait_id, item_name, provided))
    | `Assoc [ ("TraitItemDecl", `List [ x0; x1 ]) ] ->
        let* x0 = trait_decl_id_of_json x0 in
        let* x1 = trait_item_name_of_json x1 in
        Ok (TraitItemDecl (x0, x1))
    | `Assoc [ ("TraitItemProvided", `List [ x0; x1 ]) ] ->
        let* x0 = trait_decl_id_of_json x0 in
        let* x1 = trait_item_name_of_json x1 in
        Ok (TraitItemProvided (x0, x1))
    | _ -> Error "")

let maybe_opaque_body_of_json (bodies : 'body gexpr_body option list)
    (js : json) : ('body gexpr_body option, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ok", body) ] ->
        let* body_id = BodyId.id_of_json body in
        let body = List.nth bodies (BodyId.to_int body_id) in
        Ok body
    | `Assoc [ ("Err", `Null) ] -> Ok None
    | _ -> Error "")

(* This is written by hand because the corresponding rust type is not type-generic. *)
let gfun_decl_of_json (bodies : 'body gexpr_body option list)
    (id_to_file : id_to_file_map) (js : json) : ('body gfun_decl, string) result
    =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("signature", signature);
          ("kind", kind);
          ("body", body);
        ] ->
        let* def_id = FunDeclId.id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* signature = fun_sig_of_json id_to_file signature in
        let* kind = item_kind_of_json kind in
        let* body = maybe_opaque_body_of_json bodies body in
        Ok
          {
            def_id;
            item_meta;
            signature;
            kind;
            body;
            is_global_decl_body = false;
          }
    | _ -> Error "")

let rec gglobal_decl_of_json (bodies : 'body gexpr_body option list)
    (id_to_file : id_to_file_map) (js : json) :
    ('body gexpr_body option gglobal_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("generics", generics);
          ("ty", ty);
          ("kind", kind);
          ("body", body);
        ] ->
        let* global_id = GlobalDeclId.id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* generics = generic_params_of_json id_to_file generics in
        let* ty = ty_of_json ty in
        let* kind = item_kind_of_json kind in
        let* body = maybe_opaque_body_of_json bodies body in
        let global =
          { def_id = global_id; item_meta; body; generics; ty; kind }
        in
        Ok global
    | _ -> Error "")

and trait_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (trait_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("generics", generics);
          ("parent_clauses", parent_clauses);
          ("consts", consts);
          ("const_defaults", _);
          ("types", types);
          ("type_defaults", _);
          ("type_clauses", _);
          ("required_methods", required_methods);
          ("provided_methods", provided_methods);
        ] ->
        let* def_id = trait_decl_id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* generics = generic_params_of_json id_to_file generics in
        let* parent_clauses =
          vector_of_json trait_clause_id_of_json
            (trait_clause_of_json id_to_file)
            parent_clauses
        in
        let* consts =
          list_of_json (pair_of_json trait_item_name_of_json ty_of_json) consts
        in
        let* types = list_of_json trait_item_name_of_json types in
        let* required_methods =
          list_of_json
            (pair_of_json trait_item_name_of_json fun_decl_id_of_json)
            required_methods
        in
        let* provided_methods =
          list_of_json
            (pair_of_json trait_item_name_of_json
               (option_of_json fun_decl_id_of_json))
            provided_methods
        in
        Ok
          {
            def_id;
            item_meta;
            generics;
            parent_clauses;
            consts;
            types;
            required_methods;
            provided_methods;
          }
    | _ -> Error "")

and trait_impl_of_json (id_to_file : id_to_file_map) (js : json) :
    (trait_impl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("item_meta", item_meta);
          ("impl_trait", impl_trait);
          ("generics", generics);
          ("parent_trait_refs", parent_trait_refs);
          ("consts", consts);
          ("types", types);
          ("type_clauses", _);
          ("required_methods", required_methods);
          ("provided_methods", provided_methods);
        ] ->
        let* def_id = trait_impl_id_of_json def_id in
        let* item_meta = item_meta_of_json id_to_file item_meta in
        let* impl_trait = trait_decl_ref_of_json impl_trait in
        let* generics = generic_params_of_json id_to_file generics in
        let* parent_trait_refs =
          vector_of_json trait_clause_id_of_json trait_ref_of_json
            parent_trait_refs
        in
        let* consts =
          list_of_json
            (pair_of_json trait_item_name_of_json global_decl_id_of_json)
            consts
        in
        let* types =
          list_of_json (pair_of_json trait_item_name_of_json ty_of_json) types
        in
        let* required_methods =
          list_of_json
            (pair_of_json trait_item_name_of_json fun_decl_id_of_json)
            required_methods
        in
        let* provided_methods =
          list_of_json
            (pair_of_json trait_item_name_of_json fun_decl_id_of_json)
            provided_methods
        in
        Ok
          {
            def_id;
            item_meta;
            impl_trait;
            generics;
            parent_trait_refs;
            consts;
            types;
            required_methods;
            provided_methods;
          }
    | _ -> Error "")

and g_declaration_group_of_json :
      'a0.
      (json -> ('a0, string) result) ->
      json ->
      ('a0 g_declaration_group, string) result =
 fun arg0_of_json js ->
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("NonRec", non_rec) ] ->
        let* non_rec = arg0_of_json non_rec in
        Ok (NonRecGroup non_rec)
    | `Assoc [ ("Rec", rec_) ] ->
        let* rec_ = list_of_json arg0_of_json rec_ in
        Ok (RecGroup rec_)
    | _ -> Error "")

and declaration_group_of_json (js : json) : (declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Type", type_) ] ->
        let* type_ = g_declaration_group_of_json type_decl_id_of_json type_ in
        Ok (TypeGroup type_)
    | `Assoc [ ("Fun", fun_) ] ->
        let* fun_ = g_declaration_group_of_json fun_decl_id_of_json fun_ in
        Ok (FunGroup fun_)
    | `Assoc [ ("Global", global) ] ->
        let* global =
          g_declaration_group_of_json global_decl_id_of_json global
        in
        Ok (GlobalGroup global)
    | `Assoc [ ("TraitDecl", trait_decl) ] ->
        let* trait_decl =
          g_declaration_group_of_json trait_decl_id_of_json trait_decl
        in
        Ok (TraitDeclGroup trait_decl)
    | `Assoc [ ("TraitImpl", trait_impl) ] ->
        let* trait_impl =
          g_declaration_group_of_json trait_impl_id_of_json trait_impl
        in
        Ok (TraitImplGroup trait_impl)
    | `Assoc [ ("Mixed", mixed) ] ->
        let* mixed = g_declaration_group_of_json any_decl_id_of_json mixed in
        Ok (MixedGroup mixed)
    | _ -> Error "")

and any_decl_id_of_json (js : json) : (any_decl_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Fun", id) ] ->
        let* id = FunDeclId.id_of_json id in
        Ok (IdFun id)
    | `Assoc [ ("Global", id) ] ->
        let* id = GlobalDeclId.id_of_json id in
        Ok (IdGlobal id)
    | `Assoc [ ("Type", id) ] ->
        let* id = TypeDeclId.id_of_json id in
        Ok (IdType id)
    | `Assoc [ ("TraitDecl", id) ] ->
        let* id = TraitDeclId.id_of_json id in
        Ok (IdTraitDecl id)
    | `Assoc [ ("TraitImpl", id) ] ->
        let* id = TraitImplId.id_of_json id in
        Ok (IdTraitImpl id)
    | _ -> Error "")
