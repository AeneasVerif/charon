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
(* __REPLACE3__ *)

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

(* __REPLACE2__ *)

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

(* __REPLACE0__ *)
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

(* __REPLACE1__ *)

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

(* __REPLACE4__ *)

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

(* __REPLACE5__ *)

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

and gcrate_of_json
    (body_of_json : id_to_file_map -> json -> ('body gexpr_body, string) result)
    (js : json) : (('body, 'body gexpr_body option) gcrate, string) result =
  match js with
  | `Assoc
      [
        ("charon_version", charon_version);
        ("name", name);
        ("id_to_file", id_to_file);
        ("declarations", declarations);
        ("types", types);
        ("functions", functions);
        ("globals", globals);
        ("bodies", bodies);
        ("trait_decls", trait_decls);
        ("trait_impls", trait_impls);
      ] ->
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
      else
        combine_error_msgs js __FUNCTION__
          (let* name = string_of_json name in
           let* id_to_file = id_to_file_of_json id_to_file in

           let* declarations =
             list_of_json declaration_group_of_json declarations
           in

           let* bodies =
             list_of_json (option_of_json (body_of_json id_to_file)) bodies
           in
           let* types = list_of_json (type_decl_of_json id_to_file) types in
           let* functions =
             list_of_json (gfun_decl_of_json bodies id_to_file) functions
           in
           let* globals =
             list_of_json (gglobal_decl_of_json bodies id_to_file) globals
           in
           let* trait_decls =
             list_of_json (trait_decl_of_json id_to_file) trait_decls
           in
           let* trait_impls =
             list_of_json (trait_impl_of_json id_to_file) trait_impls
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
                  (fun (d : 'body gexpr_body option gglobal_decl) ->
                    (d.def_id, d))
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
             })
  | _ -> combine_error_msgs js __FUNCTION__ (Error "")
