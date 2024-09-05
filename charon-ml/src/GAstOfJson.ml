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
module FileId = IdGen ()

(** The default logger *)
let log = Logging.llbc_of_json_logger

(** A file identifier *)
type file_id = FileId.id [@@deriving show, ord]

type id_to_file_map = file_name FileId.Map.t

let de_bruijn_id_of_json = int_of_json
let path_buf_of_json = string_of_json
let trait_item_name_of_json = string_of_json
let const_generic_var_id_of_json = ConstGenericVarId.id_of_json
let disambiguator_of_json = Disambiguator.id_of_json
let field_id_of_json = FieldId.id_of_json
let fun_decl_id_of_json = FunDeclId.id_of_json
let global_decl_id_of_json = GlobalDeclId.id_of_json
let file_id_of_json = FileId.id_of_json
let region_id_of_json = RegionVarId.id_of_json
let trait_clause_id_of_json = TraitClauseId.id_of_json
let trait_decl_id_of_json = TraitDeclId.id_of_json
let trait_impl_id_of_json = TraitImplId.id_of_json
let type_decl_id_of_json = TypeDeclId.id_of_json
let type_var_id_of_json = TypeVarId.id_of_json
let variant_id_of_json = VariantId.id_of_json
let var_id_of_json = VarId.id_of_json

(* A vector can contain empty slots. We filter them out. *)
let vector_of_json _ item_of_json js =
  let* list = list_of_json (option_of_json item_of_json) js in
  Ok (List.filter_map (fun x -> x) list)

(** Deserialize a map from file id to file name.

    In the serialized LLBC, the files in the loc spans are refered to by their
    ids, in order to save space. In a functional language like OCaml this is
    not necessary: we thus replace the file ids by the file name themselves in
    the AST.
    The "id to file" map is thus only used in the deserialization process.
  *)
let rec id_to_file_of_json (js : json) : (id_to_file_map, string) result =
  combine_error_msgs js __FUNCTION__
    ((* The map is stored as a list of pairs (key, value): we deserialize
      * this list then convert it to a map *)
     let* file_names = list_of_json (option_of_json file_name_of_json) js in
     let names_with_ids =
       List.filter_map
         (fun (i, name) ->
           match name with None -> None | Some name -> Some (i, name))
         (List.mapi (fun i name -> (FileId.of_int i, name)) file_names)
     in
     Ok (FileId.Map.of_list names_with_ids))

(* This is written by hand because it accessed `id_to_file`. *)
and raw_span_of_json (id_to_file : id_to_file_map) (js : json) :
    (raw_span, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("file_id", file_id); ("beg", beg_loc); ("end", end_loc) ] ->
        let* file_id = file_id_of_json file_id in
        let file = FileId.Map.find file_id id_to_file in
        let* beg_loc = loc_of_json beg_loc in
        let* end_loc = loc_of_json end_loc in
        Ok { file; beg_loc; end_loc }
    | _ -> Error "")

and big_int_of_json (js : json) : (big_int, string) result =
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
and scalar_value_of_json (js : json) : (scalar_value, string) result =
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

and maybe_opaque_body_of_json (bodies : 'body gexpr_body option list)
    (js : json) : ('body gexpr_body option, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ok", body) ] ->
        let* body_id = BodyId.id_of_json body in
        let body = List.nth bodies (BodyId.to_int body_id) in
        Ok body
    | `Assoc [ ("Err", `Null) ] -> Ok None
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

and loc_of_json (js : json) : (loc, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("line", line); ("col", col) ] ->
        let* line = int_of_json line in
        let* col = int_of_json col in
        Ok ({ line; col } : loc)
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
        Ok ({ span; generated_from_span } : span)
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
    | `Assoc [ ("DocComment", doc_comment) ] ->
        let* doc_comment = string_of_json doc_comment in
        Ok (AttrDocComment doc_comment)
    | `Assoc [ ("Unknown", unknown) ] ->
        let* unknown = raw_attribute_of_json unknown in
        Ok (AttrUnknown unknown)
    | _ -> Error "")

and raw_attribute_of_json (js : json) : (raw_attribute, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("path", path); ("args", args) ] ->
        let* path = string_of_json path in
        let* args = option_of_json string_of_json args in
        Ok ({ path; args } : raw_attribute)
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
        Ok ({ attributes; inline; rename; public } : attr_info)
    | _ -> Error "")

and type_var_of_json (js : json) : (type_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = type_var_id_of_json index in
        let* name = string_of_json name in
        Ok ({ index; name } : type_var)
    | _ -> Error "")

and region_var_of_json (js : json) : (region_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = region_id_of_json index in
        let* name = option_of_json string_of_json name in
        Ok ({ index; name } : region_var)
    | _ -> Error "")

and region_of_json (js : json) : (region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Static" -> Ok RStatic
    | `Assoc [ ("BVar", `List [ x_0; x_1 ]) ] ->
        let* x_0 = de_bruijn_id_of_json x_0 in
        let* x_1 = region_id_of_json x_1 in
        Ok (RBVar (x_0, x_1))
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

and float_type_of_json (js : json) : (float_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "F16" -> Ok F16
    | `String "F32" -> Ok F32
    | `String "F64" -> Ok F64
    | `String "F128" -> Ok F128
    | _ -> Error "")

and literal_type_of_json (js : json) : (literal_type, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Integer", integer) ] ->
        let* integer = integer_type_of_json integer in
        Ok (TInteger integer)
    | `Assoc [ ("Float", float) ] ->
        let* float = float_type_of_json float in
        Ok (TFloat float)
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
        Ok ({ index; name; ty } : const_generic_var)
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
    | `Assoc [ ("Builtin", builtin) ] ->
        let* builtin = assumed_ty_of_json builtin in
        Ok (TAssumed builtin)
    | _ -> Error "")

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
    | `Assoc [ ("Adt", `List [ x_0; x_1 ]) ] ->
        let* x_0 = type_id_of_json x_0 in
        let* x_1 = generic_args_of_json x_1 in
        Ok (TAdt (x_0, x_1))
    | `Assoc [ ("TypeVar", type_var) ] ->
        let* type_var = type_var_id_of_json type_var in
        Ok (TVar type_var)
    | `Assoc [ ("Literal", literal) ] ->
        let* literal = literal_type_of_json literal in
        Ok (TLiteral literal)
    | `String "Never" -> Ok TNever
    | `Assoc [ ("Ref", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = region_of_json x_0 in
        let* x_1 = ty_of_json x_1 in
        let* x_2 = ref_kind_of_json x_2 in
        Ok (TRef (x_0, x_1, x_2))
    | `Assoc [ ("RawPtr", `List [ x_0; x_1 ]) ] ->
        let* x_0 = ty_of_json x_0 in
        let* x_1 = ref_kind_of_json x_1 in
        Ok (TRawPtr (x_0, x_1))
    | `Assoc [ ("TraitType", `List [ x_0; x_1 ]) ] ->
        let* x_0 = trait_ref_of_json x_0 in
        let* x_1 = trait_item_name_of_json x_1 in
        Ok (TTraitType (x_0, x_1))
    | `Assoc [ ("DynTrait", dyn_trait) ] ->
        let* dyn_trait = existential_predicate_of_json dyn_trait in
        Ok (TDynTrait dyn_trait)
    | `Assoc [ ("Arrow", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = vector_of_json region_id_of_json region_var_of_json x_0 in
        let* x_1 = list_of_json ty_of_json x_1 in
        let* x_2 = ty_of_json x_2 in
        Ok (TArrow (x_0, x_1, x_2))
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
        Ok ({ trait_id; trait_decl_ref } : trait_ref)
    | _ -> Error "")

and trait_decl_ref_of_json (js : json) : (trait_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("trait_id", trait_id); ("generics", generics) ] ->
        let* trait_decl_id = trait_decl_id_of_json trait_id in
        let* decl_generics = generic_args_of_json generics in
        Ok ({ trait_decl_id; decl_generics } : trait_decl_ref)
    | _ -> Error "")

and global_decl_ref_of_json (js : json) : (global_decl_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("generics", generics) ] ->
        let* global_id = global_decl_id_of_json id in
        let* global_generics = generic_args_of_json generics in
        Ok ({ global_id; global_generics } : global_decl_ref)
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
        let* regions =
          vector_of_json region_id_of_json region_of_json regions
        in
        let* types = vector_of_json type_var_id_of_json ty_of_json types in
        let* const_generics =
          vector_of_json const_generic_var_id_of_json const_generic_of_json
            const_generics
        in
        let* trait_refs =
          vector_of_json trait_clause_id_of_json trait_ref_of_json trait_refs
        in
        Ok ({ regions; types; const_generics; trait_refs } : generic_args)
    | _ -> Error "")

and trait_instance_id_of_json (js : json) : (trait_instance_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("TraitImpl", `List [ x_0; x_1 ]) ] ->
        let* x_0 = trait_impl_id_of_json x_0 in
        let* x_1 = generic_args_of_json x_1 in
        Ok (TraitImpl (x_0, x_1))
    | `Assoc [ ("Clause", clause) ] ->
        let* clause = trait_clause_id_of_json clause in
        Ok (Clause clause)
    | `Assoc [ ("ParentClause", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = trait_instance_id_of_json x_0 in
        let* x_1 = trait_decl_id_of_json x_1 in
        let* x_2 = trait_clause_id_of_json x_2 in
        Ok (ParentClause (x_0, x_1, x_2))
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
        Ok ({ span; attr_info; field_name; field_ty } : field)
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
        Ok ({ span; attr_info; variant_name; fields; discriminant } : variant)
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
    | `Assoc [ ("Union", union) ] ->
        let* union =
          vector_of_json field_id_of_json (field_of_json id_to_file) union
        in
        Ok (Union union)
    | `String "Opaque" -> Ok Opaque
    | `Assoc [ ("Alias", alias) ] ->
        let* alias = ty_of_json alias in
        Ok (Alias alias)
    | `Assoc [ ("Error", error) ] ->
        let* error = string_of_json error in
        Ok (Error error)
    | _ -> Error "")

and trait_clause_of_json (id_to_file : id_to_file_map) (js : json) :
    (trait_clause, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("clause_id", clause_id);
          ("span", span);
          ("origin", _);
          ("trait_", trait);
        ] ->
        let* clause_id = trait_clause_id_of_json clause_id in
        let* span = option_of_json (span_of_json id_to_file) span in
        let* trait = trait_decl_ref_of_json trait in
        Ok ({ clause_id; span; trait } : trait_clause)
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
    | `List [ x_0; x_1 ] ->
        let* x_0 = arg0_of_json x_0 in
        let* x_1 = arg1_of_json x_1 in
        Ok (x_0, x_1)
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
        Ok ({ trait_ref; type_name; ty } : trait_type_constraint)
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
          ({
             regions;
             types;
             const_generics;
             trait_clauses;
             regions_outlive;
             types_outlive;
             trait_type_constraints;
           }
            : generic_params)
    | _ -> Error "")

and impl_elem_of_json (id_to_file : id_to_file_map) (js : json) :
    (impl_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ty", `List [ x_0; x_1 ]) ] ->
        let* x_0 = generic_params_of_json id_to_file x_0 in
        let* x_1 = ty_of_json x_1 in
        Ok (ImplElemTy (x_0, x_1))
    | `Assoc [ ("Trait", trait) ] ->
        let* trait = trait_impl_id_of_json trait in
        Ok (ImplElemTrait trait)
    | _ -> Error "")

and path_elem_of_json (id_to_file : id_to_file_map) (js : json) :
    (path_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ident", `List [ x_0; x_1 ]) ] ->
        let* x_0 = string_of_json x_0 in
        let* x_1 = disambiguator_of_json x_1 in
        Ok (PeIdent (x_0, x_1))
    | `Assoc [ ("Impl", `List [ x_0; x_1 ]) ] ->
        let* x_0 = impl_elem_of_json id_to_file x_0 in
        let* x_1 = disambiguator_of_json x_1 in
        Ok (PeImpl (x_0, x_1))
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
          ("name", name);
          ("span", span);
          ("source_text", source_text);
          ("attr_info", attr_info);
          ("is_local", is_local);
          ("opacity", _);
        ] ->
        let* name = name_of_json id_to_file name in
        let* span = span_of_json id_to_file span in
        let* source_text = option_of_json string_of_json source_text in
        let* attr_info = attr_info_of_json attr_info in
        let* is_local = bool_of_json is_local in
        Ok ({ name; span; source_text; attr_info; is_local } : item_meta)
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
        Ok ({ def_id; item_meta; generics; kind } : type_decl)
    | _ -> Error "")

and var_of_json (js : json) : (var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = var_id_of_json index in
        let* name = option_of_json string_of_json name in
        let* var_ty = ty_of_json ty in
        Ok ({ index; name; var_ty } : var)
    | _ -> Error "")

and field_proj_kind_of_json (js : json) : (field_proj_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ x_0; x_1 ]) ] ->
        let* x_0 = type_decl_id_of_json x_0 in
        let* x_1 = option_of_json variant_id_of_json x_1 in
        Ok (ProjAdt (x_0, x_1))
    | `Assoc [ ("Tuple", tuple) ] ->
        let* tuple = int_of_json tuple in
        Ok (ProjTuple tuple)
    | _ -> Error "")

and projection_elem_of_json (js : json) : (projection_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Deref" -> Ok Deref
    | `Assoc [ ("Field", `List [ x_0; x_1 ]) ] ->
        let* x_0 = field_proj_kind_of_json x_0 in
        let* x_1 = field_id_of_json x_1 in
        Ok (Field (x_0, x_1))
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
        Ok ({ var_id; projection } : place)
    | _ -> Error "")

and borrow_kind_of_json (js : json) : (borrow_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Shared" -> Ok BShared
    | `String "Mut" -> Ok BMut
    | `String "TwoPhaseMut" -> Ok BTwoPhaseMut
    | `String "Shallow" -> Ok BShallow
    | `String "UniqueImmutable" -> Ok BUniqueImmutable
    | _ -> Error "")

and cast_kind_of_json (js : json) : (cast_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", `List [ x_0; x_1 ]) ] ->
        let* x_0 = literal_type_of_json x_0 in
        let* x_1 = literal_type_of_json x_1 in
        Ok (CastScalar (x_0, x_1))
    | `Assoc [ ("RawPtr", `List [ x_0; x_1 ]) ] ->
        let* x_0 = ty_of_json x_0 in
        let* x_1 = ty_of_json x_1 in
        Ok (CastRawPtr (x_0, x_1))
    | `Assoc [ ("FnPtr", `List [ x_0; x_1 ]) ] ->
        let* x_0 = ty_of_json x_0 in
        let* x_1 = ty_of_json x_1 in
        Ok (CastFnPtr (x_0, x_1))
    | `Assoc [ ("Unsize", `List [ x_0; x_1 ]) ] ->
        let* x_0 = ty_of_json x_0 in
        let* x_1 = ty_of_json x_1 in
        Ok (CastUnsize (x_0, x_1))
    | `Assoc [ ("Transmute", `List [ x_0; x_1 ]) ] ->
        let* x_0 = ty_of_json x_0 in
        let* x_1 = ty_of_json x_1 in
        Ok (CastTransmute (x_0, x_1))
    | _ -> Error "")

and abort_kind_of_json (id_to_file : id_to_file_map) (js : json) :
    (abort_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Panic", panic) ] ->
        let* panic = name_of_json id_to_file panic in
        Ok (Panic panic)
    | `String "UndefinedBehavior" -> Ok UndefinedBehavior
    | _ -> Error "")

and assertion_of_json (js : json) : (assertion, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("cond", cond); ("expected", expected) ] ->
        let* cond = operand_of_json cond in
        let* expected = bool_of_json expected in
        Ok ({ cond; expected } : assertion)
    | _ -> Error "")

and nullop_of_json (js : json) : (nullop, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "SizeOf" -> Ok SizeOf
    | `String "AlignOf" -> Ok AlignOf
    | `Assoc [ ("OffsetOf", offset_of) ] ->
        let* offset_of =
          list_of_json (pair_of_json int_of_json field_id_of_json) offset_of
        in
        Ok (OffsetOf offset_of)
    | `String "UbChecks" -> Ok UbChecks
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
    | `String "ArrayToSliceShared" -> Ok ArrayToSliceShared
    | `String "ArrayToSliceMut" -> Ok ArrayToSliceMut
    | `String "ArrayRepeat" -> Ok ArrayRepeat
    | `Assoc [ ("Index", index) ] ->
        let* index = builtin_index_op_of_json index in
        Ok (Index index)
    | _ -> Error "")

and builtin_index_op_of_json (js : json) : (builtin_index_op, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("is_array", is_array);
          ("mutability", mutability);
          ("is_range", is_range);
        ] ->
        let* is_array = bool_of_json is_array in
        let* mutability = ref_kind_of_json mutability in
        let* is_range = bool_of_json is_range in
        Ok ({ is_array; mutability; is_range } : builtin_index_op)
    | _ -> Error "")

and fun_id_of_json (js : json) : (fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", regular) ] ->
        let* regular = fun_decl_id_of_json regular in
        Ok (FRegular regular)
    | `Assoc [ ("Builtin", builtin) ] ->
        let* builtin = assumed_fun_id_of_json builtin in
        Ok (FAssumed builtin)
    | _ -> Error "")

and fun_id_or_trait_method_ref_of_json (js : json) :
    (fun_id_or_trait_method_ref, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Fun", fun_) ] ->
        let* fun_ = fun_id_of_json fun_ in
        Ok (FunId fun_)
    | `Assoc [ ("Trait", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = trait_ref_of_json x_0 in
        let* x_1 = trait_item_name_of_json x_1 in
        let* x_2 = fun_decl_id_of_json x_2 in
        Ok (TraitMethod (x_0, x_1, x_2))
    | _ -> Error "")

and fn_ptr_of_json (js : json) : (fn_ptr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("func", func); ("generics", generics) ] ->
        let* func = fun_id_or_trait_method_ref_of_json func in
        let* generics = generic_args_of_json generics in
        Ok ({ func; generics } : fn_ptr)
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
        Ok ({ value; ty } : constant_expr)
    | _ -> Error "")

and raw_constant_expr_of_json (js : json) : (raw_constant_expr, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Literal", literal) ] ->
        let* literal = literal_of_json literal in
        Ok (CLiteral literal)
    | `Assoc [ ("TraitConst", `List [ x_0; x_1 ]) ] ->
        let* x_0 = trait_ref_of_json x_0 in
        let* x_1 = trait_item_name_of_json x_1 in
        Ok (CTraitConst (x_0, x_1))
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
    | `Assoc [ ("Adt", `List [ x_0; x_1; x_2; x_3 ]) ] ->
        let* x_0 = type_id_of_json x_0 in
        let* x_1 = option_of_json variant_id_of_json x_1 in
        let* x_2 = option_of_json field_id_of_json x_2 in
        let* x_3 = generic_args_of_json x_3 in
        Ok (AggregatedAdt (x_0, x_1, x_2, x_3))
    | `Assoc [ ("Array", `List [ x_0; x_1 ]) ] ->
        let* x_0 = ty_of_json x_0 in
        let* x_1 = const_generic_of_json x_1 in
        Ok (AggregatedArray (x_0, x_1))
    | `Assoc [ ("Closure", `List [ x_0; x_1 ]) ] ->
        let* x_0 = fun_decl_id_of_json x_0 in
        let* x_1 = generic_args_of_json x_1 in
        Ok (AggregatedClosure (x_0, x_1))
    | _ -> Error "")

and rvalue_of_json (js : json) : (rvalue, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Use", use) ] ->
        let* use = operand_of_json use in
        Ok (Use use)
    | `Assoc [ ("Ref", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json x_0 in
        let* x_1 = borrow_kind_of_json x_1 in
        Ok (RvRef (x_0, x_1))
    | `Assoc [ ("RawPtr", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json x_0 in
        let* x_1 = ref_kind_of_json x_1 in
        Ok (RawPtr (x_0, x_1))
    | `Assoc [ ("BinaryOp", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = binop_of_json x_0 in
        let* x_1 = operand_of_json x_1 in
        let* x_2 = operand_of_json x_2 in
        Ok (BinaryOp (x_0, x_1, x_2))
    | `Assoc [ ("UnaryOp", `List [ x_0; x_1 ]) ] ->
        let* x_0 = unop_of_json x_0 in
        let* x_1 = operand_of_json x_1 in
        Ok (UnaryOp (x_0, x_1))
    | `Assoc [ ("NullaryOp", `List [ x_0; x_1 ]) ] ->
        let* x_0 = nullop_of_json x_0 in
        let* x_1 = ty_of_json x_1 in
        Ok (NullaryOp (x_0, x_1))
    | `Assoc [ ("Discriminant", `List [ x_0; x_1 ]) ] ->
        let* x_0 = place_of_json x_0 in
        let* x_1 = type_decl_id_of_json x_1 in
        Ok (Discriminant (x_0, x_1))
    | `Assoc [ ("Aggregate", `List [ x_0; x_1 ]) ] ->
        let* x_0 = aggregate_kind_of_json x_0 in
        let* x_1 = list_of_json operand_of_json x_1 in
        Ok (Aggregate (x_0, x_1))
    | `Assoc [ ("Global", global) ] ->
        let* global = global_decl_ref_of_json global in
        Ok (Global global)
    | `Assoc [ ("GlobalRef", `List [ x_0; x_1 ]) ] ->
        let* x_0 = global_decl_ref_of_json x_0 in
        let* x_1 = ref_kind_of_json x_1 in
        Ok (GlobalRef (x_0, x_1))
    | `Assoc [ ("Len", `List [ x_0; x_1; x_2 ]) ] ->
        let* x_0 = place_of_json x_0 in
        let* x_1 = ty_of_json x_1 in
        let* x_2 = option_of_json const_generic_of_json x_2 in
        Ok (Len (x_0, x_1, x_2))
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
          ({
             num_region_params;
             num_type_params;
             num_const_generic_params;
             num_trait_clauses;
             num_regions_outlive;
             num_types_outlive;
             num_trait_type_constraints;
           }
            : params_info)
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
        let* state = vector_of_json type_var_id_of_json ty_of_json state in
        Ok ({ kind; state } : closure_info)
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
          ({
             is_unsafe;
             is_closure;
             closure_info;
             generics;
             parent_params_info;
             inputs;
             output;
           }
            : fun_sig)
    | _ -> Error "")

and call_of_json (js : json) : (call, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("func", func); ("args", args); ("dest", dest) ] ->
        let* func = fn_operand_of_json func in
        let* args = list_of_json operand_of_json args in
        let* dest = place_of_json dest in
        Ok ({ func; args; dest } : call)
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
        Ok ({ span; arg_count; locals; body } : _ gexpr_body)
    | _ -> Error "")

and item_kind_of_json (js : json) : (item_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Regular" -> Ok RegularItem
    | `Assoc
        [
          ( "TraitDecl",
            `Assoc
              [
                ("trait_id", trait_id);
                ("item_name", item_name);
                ("has_default", has_default);
              ] );
        ] ->
        let* trait_id = trait_decl_id_of_json trait_id in
        let* item_name = trait_item_name_of_json item_name in
        let* has_default = bool_of_json has_default in
        Ok (TraitDeclItem (trait_id, item_name, has_default))
    | `Assoc
        [
          ( "TraitImpl",
            `Assoc
              [
                ("impl_id", impl_id);
                ("trait_id", trait_id);
                ("item_name", item_name);
                ("reuses_default", reuses_default);
              ] );
        ] ->
        let* impl_id = trait_impl_id_of_json impl_id in
        let* trait_id = trait_decl_id_of_json trait_id in
        let* item_name = trait_item_name_of_json item_name in
        let* reuses_default = bool_of_json reuses_default in
        Ok (TraitImplItem (impl_id, trait_id, item_name, reuses_default))
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
            (pair_of_json trait_item_name_of_json fun_decl_id_of_json)
            provided_methods
        in
        Ok
          ({
             def_id;
             item_meta;
             generics;
             parent_clauses;
             consts;
             types;
             required_methods;
             provided_methods;
           }
            : trait_decl)
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
            (pair_of_json trait_item_name_of_json global_decl_ref_of_json)
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
          ({
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
            : trait_impl)
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
    | `Assoc [ ("Type", type_) ] ->
        let* type_ = type_decl_id_of_json type_ in
        Ok (IdType type_)
    | `Assoc [ ("Fun", fun_) ] ->
        let* fun_ = fun_decl_id_of_json fun_ in
        Ok (IdFun fun_)
    | `Assoc [ ("Global", global) ] ->
        let* global = global_decl_id_of_json global in
        Ok (IdGlobal global)
    | `Assoc [ ("TraitDecl", trait_decl) ] ->
        let* trait_decl = trait_decl_id_of_json trait_decl in
        Ok (IdTraitDecl trait_decl)
    | `Assoc [ ("TraitImpl", trait_impl) ] ->
        let* trait_impl = trait_impl_id_of_json trait_impl in
        Ok (IdTraitImpl trait_impl)
    | _ -> Error "")

(* This is written by hand because the corresponding rust type is not type-generic. *)
and gfun_decl_of_json (bodies : 'body gexpr_body option list)
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

and gglobal_decl_of_json (bodies : 'body gexpr_body option list)
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

(* This is written by hand because the corresponding rust type is not type-generic. *)
and gtranslated_crate_of_json
    (body_of_json : id_to_file_map -> json -> ('body gexpr_body, string) result)
    (js : json) : (('body, 'body gexpr_body option) gcrate, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("crate_name", name);
          ("real_crate_name", _);
          ("id_to_file", id_to_file);
          ("all_ids", _);
          ("item_names", _);
          ("type_decls", types);
          ("fun_decls", functions);
          ("global_decls", globals);
          ("bodies", bodies);
          ("trait_decls", trait_decls);
          ("trait_impls", trait_impls);
          ("ordered_decls", declarations);
        ] ->
        let* name = string_of_json name in
        let* id_to_file = id_to_file_of_json id_to_file in

        let* declarations =
          list_of_json declaration_group_of_json declarations
        in

        let* bodies =
          list_of_json (option_of_json (body_of_json id_to_file)) bodies
        in
        let* types =
          vector_of_json type_id_of_json (type_decl_of_json id_to_file) types
        in
        let* functions =
          vector_of_json fun_decl_id_of_json
            (gfun_decl_of_json bodies id_to_file)
            functions
        in
        let* globals =
          vector_of_json global_decl_id_of_json
            (gglobal_decl_of_json bodies id_to_file)
            globals
        in
        let* trait_decls =
          vector_of_json trait_decl_id_of_json
            (trait_decl_of_json id_to_file)
            trait_decls
        in
        let* trait_impls =
          vector_of_json trait_impl_id_of_json
            (trait_impl_of_json id_to_file)
            trait_impls
        in

        let type_decls =
          TypeDeclId.Map.of_list
            (List.map (fun (d : type_decl) -> (d.def_id, d)) types)
        in
        let fun_decls =
          FunDeclId.Map.of_list
            (List.map (fun (d : 'body gfun_decl) -> (d.def_id, d)) functions)
        in
        let global_decls =
          GlobalDeclId.Map.of_list
            (List.map
               (fun (d : 'body gexpr_body option gglobal_decl) -> (d.def_id, d))
               globals)
        in
        let trait_decls =
          TraitDeclId.Map.of_list
            (List.map (fun (d : trait_decl) -> (d.def_id, d)) trait_decls)
        in
        let trait_impls =
          TraitImplId.Map.of_list
            (List.map (fun (d : trait_impl) -> (d.def_id, d)) trait_impls)
        in

        Ok
          {
            name;
            declarations;
            type_decls;
            fun_decls;
            global_decls;
            trait_decls;
            trait_impls;
          }
    | _ -> Error "")

and gcrate_of_json
    (body_of_json : id_to_file_map -> json -> ('body gexpr_body, string) result)
    (js : json) : (('body, 'body gexpr_body option) gcrate, string) result =
  match js with
  | `Assoc [ ("charon_version", charon_version); ("translated", translated) ] ->
      (* Ensure the version is the one we support. *)
      let* charon_version = string_of_json charon_version in
      if
        not (String.equal charon_version CharonVersion.supported_charon_version)
      then
        Error
          ("Incompatible version of charon: this program supports llbc emitted \
            by charon v" ^ CharonVersion.supported_charon_version
         ^ " but attempted to read a file emitted by charon v" ^ charon_version
         ^ ".")
      else gtranslated_crate_of_json body_of_json translated
  | _ -> combine_error_msgs js __FUNCTION__ (Error "")
