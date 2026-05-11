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
        Format.kasprintf Result.error
          "Incompatible version of charon: this program supports llbc emitted \
           by charon v%s but attempted to read a file emitted by charon v%s."
          CharonVersion.supported_charon_version charon_version
      else
        let ctx = empty_of_json_ctx in
        let* crate = translated_crate_of_json ctx translated in
        Ok
          {
            name = crate.crate_name;
            options = crate.options;
            target_information = crate.target_information;
            declarations = Option.value ~default:[] crate.ordered_decls;
            type_decls = crate.type_decls;
            fun_decls = crate.fun_decls;
            global_decls = crate.global_decls;
            trait_decls = crate.trait_decls;
            trait_impls = crate.trait_impls;
          }
  | _ -> combine_error_msgs js __FUNCTION__ (Error "")

let crate_of_json_file (file : string) : (crate, string) result =
  let* format = OfPostcardBasic.format_hint_of_file file in
  match format with
  | Json ->
      let json = Yojson.Basic.from_file file in
      crate_of_json json
  | Postcard ->
      Format.kasprintf Result.error
        "This file looks like Postcard, but JSON deserialization was \
         requested: %s. Please use Postcard deserialization or regenerate as \
         JSON."
        file
  | Empty -> Error ("Input file is empty: " ^ file)
