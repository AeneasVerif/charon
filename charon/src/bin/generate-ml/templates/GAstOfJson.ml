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
type file_id = FileId.id
[@@deriving show, ord]

type id_to_file_map = file_name FileId.Map.t

let de_bruijn_id_of_json = int_of_json
let path_buf_of_json = string_of_json
let region_id_of_json = RegionVarId.id_of_json

(* __REPLACE0__ *)

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

(** Deserialize a map from file id to file name.

    In the serialized LLBC, the files in the loc spans are refered to by their
    ids, in order to save space. In a functional language like OCaml this is
    not necessary: we thus replace the file ids by the file name themselves in
    the AST.
    The "id to file" map is thus only used in the deserialization process.
  *)
and id_to_file_of_json (js : json) : (id_to_file_map, string) result =
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

(* This is written by hand because the corresponding rust type is not type-generic. *)
and gtranslated_crate_of_json
    (body_of_json : id_to_file_map -> json -> ('body gexpr_body, string) result)
    (js : json) : ('body gcrate, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("crate_name", name);
          ("real_crate_name", _);
          ("file_id_to_content", file_id_to_content);
          ("all_ids", _);
          ("item_names", _);
          ("id_to_file", id_to_file);
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
            (global_decl_of_json id_to_file)
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
        let* source_files =
          list_of_json
            (key_value_pair_of_json file_id_of_json string_of_json)
            file_id_to_content
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
            (List.map (fun (d : global_decl) -> (d.def_id, d)) globals)
        in
        let trait_decls =
          TraitDeclId.Map.of_list
            (List.map (fun (d : trait_decl) -> (d.def_id, d)) trait_decls)
        in
        let trait_impls =
          TraitImplId.Map.of_list
            (List.map (fun (d : trait_impl) -> (d.def_id, d)) trait_impls)
        in
        let source_files =
          FileNameMap.of_list
            (List.filter_map
               (fun (file_id, content) ->
                 Option.map
                   (fun filename -> (filename, content))
                   (FileId.Map.find_opt file_id id_to_file))
               source_files)
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
            source_files;
          }
    | _ -> Error "")

and gcrate_of_json
    (body_of_json : id_to_file_map -> json -> ('body gexpr_body, string) result)
    (js : json) : ('body gcrate, string) result =
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
