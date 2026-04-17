(** WARNING: this file is partially auto-generated. Do not edit `OfJson.ml`
    by hand. Edit `templates/OfJson.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templates/OfJson.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

open Yojson.Basic
open OfJsonBasic
open Identifiers
open Generated_Meta
open Generated_Values
open Generated_Types
open Generated_Expressions
open Generated_GAst
open Generated_FullAst
open Scalars
module FileId = IdGen ()
module HashConsId = IdGen ()

(** The default logger *)
let log = Logging.llbc_of_json_logger

module FileTbl = Hashtbl.Make (struct
  type t = FileId.id

  let equal = FileId.equal_id
  let hash = Hashtbl.hash
end)

type of_json_ctx = {
  id_to_file_map : file FileTbl.t;
  ty_hashcons_map : ty HashConsId.Map.t ref;
  tref_hashcons_map : trait_ref HashConsId.Map.t ref;
}

let empty_of_json_ctx : of_json_ctx =
  {
    id_to_file_map = FileTbl.create 8;
    ty_hashcons_map = ref HashConsId.Map.empty;
    tref_hashcons_map = ref HashConsId.Map.empty;
  }

let hash_consed_val_of_json (map : 'a HashConsId.Map.t ref)
    (of_json : of_json_ctx -> json -> ('a, string) result) (ctx : of_json_ctx)
    (js : json) : ('a, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Untagged", json) ] -> of_json ctx json
    | `Assoc [ ("HashConsedValue", `List [ `Int id; json ]) ] ->
        let* v = of_json ctx json in
        let id = HashConsId.of_int id in
        map := HashConsId.Map.add id v !map;
        Ok v
    | `Assoc [ ("Deduplicated", `Int id) ] -> begin
        let id = HashConsId.of_int id in
        match HashConsId.Map.find_opt id !map with
        | Some v -> Ok v
        | None ->
            Error
              "Hash-consing key not found; there is a serialization mismatch \
               between Rust and OCaml"
      end
    | _ -> Error "")

let path_buf_of_json = string_of_json

let big_int_of_json _ (js : json) : (big_int, string) result =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Int i -> Ok (Z.of_int i)
      | `String is -> Ok (Z.of_string is)
      | _ -> Error "")

let opt_indexed_map_of_json :
    'a0 'a1.
    (of_json_ctx -> json -> ('a0, string) result) ->
    (of_json_ctx -> json -> ('a1, string) result) ->
    of_json_ctx ->
    json ->
    ( 'a1 option list, string) result =
 fun arg0_of_json arg1_of_json ctx js ->
  list_of_json (option_of_json arg1_of_json) ctx js


(* __REPLACE0__ *)

module Ullbc = struct
  open UllbcAst

  (* __REPLACE1__ *)
end

module Llbc = struct
  open LlbcAst

  (* __REPLACE2__ *)
end

(* __REPLACE3__ *)
