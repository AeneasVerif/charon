(** Functions to load (U)LLBC ASTs from json.

    Initially, we used [ppx_derive_yojson] to automate this. However,
    [ppx_derive_yojson] expects formatting to be slightly different from what
    [serde_rs] generates (because it uses [Yojson.Safe.t] and not
    [Yojson.Basic.t]). *)

open Yojson.Basic
open OfJsonBasic
open Identifiers
open Meta
open Values
open Types
open Scalars
open Expressions
open GAst
include Generated_OfJson

let option_list_of_json of_json = list_of_json (option_of_json of_json)

(** Deserialize a map from file id to file name.

    In the serialized LLBC, the files in the loc spans are refered to by their
    ids, in order to save space. In a functional language like OCaml this is not
    necessary: we thus replace the file ids by the file name themselves in the
    AST. The "id to file" map is thus only used in the deserialization process.
*)
and id_to_file_of_json (ctx : of_json_ctx) (js : json) :
    (of_json_ctx, string) result =
  combine_error_msgs js __FUNCTION__
    ((* The map is stored as a list of pairs (key, value): we deserialize
      * this list then convert it to a map *)
     let* files = list_of_json (option_of_json file_of_json) ctx js in
     let files_with_ids =
       List.filter_map
         (fun (i, file) ->
           match file with
           | None -> None
           | Some file -> Some (i, file))
         (List.mapi (fun i file -> (FileId.of_int i, file)) files)
     in
     let id_to_file_map = FileId.Map.of_list files_with_ids in
     Ok { ctx with id_to_file_map })

let crate_of_json (js : json) : (crate, string) result =
  match js with
  | `Assoc [ ("charon_version", charon_version); ("translated", translated) ]
  | `Assoc [ ("charon_version", charon_version); ("translated", translated); _ ]
    ->
      (* Ensure the version is the one we support. *)
      let* charon_version = string_of_json () charon_version in
      if
        not (String.equal charon_version CharonVersion.supported_charon_version)
      then
        Error
          ("Incompatible version of charon: this program supports llbc emitted \
            by charon v" ^ CharonVersion.supported_charon_version
         ^ " but attempted to read a file emitted by charon v" ^ charon_version
         ^ ".")
      else
        let ctx = empty_of_json_ctx in
        let* crate = translated_crate_of_json ctx translated in
        failwith
          "TEMP: the below can't compile, because they are 'a list and not 'a \
           option list"
      (* let type_decls = TypeDeclId.map_of_indexed_list crate.type_decls in
        let fun_decls = FunDeclId.map_of_indexed_list crate.fun_decls in
        let global_decls =
          GlobalDeclId.map_of_indexed_list crate.global_decls
        in
        let trait_decls = TraitDeclId.map_of_indexed_list crate.trait_decls in
        let trait_impls = TraitImplId.map_of_indexed_list crate.trait_impls in
          Ok
          {
            name = crate.crate_name;
            options = crate.options;
            target_information = crate.target_information;
            declarations = Option.value ~default:[] crate.ordered_decls;
            type_decls;
            fun_decls;
            global_decls;
            trait_decls;
            trait_impls;
            unit_metadata = Option.get crate.unit_metadata;
            }
            *)
  | _ -> combine_error_msgs js __FUNCTION__ (Error "")
