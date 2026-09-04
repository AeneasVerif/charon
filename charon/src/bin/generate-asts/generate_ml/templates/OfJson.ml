(** WARNING: this file is partially auto-generated. Do not edit `OfJson.ml`
    by hand. Edit `generate_ml/templates/OfJson.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/OfJson.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`.
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
module DedupId = IdGen ()

(** The default logger *)
let log = Logging.llbc_of_json_logger

module FileTbl = Hashtbl.Make (struct
  type t = FileId.id

  let equal = FileId.equal_id
  let hash = Hashtbl.hash
end)

(** Table of the values that were deduplicated in the serialized output, by id. *)
module DedupTbl = Hashtbl.Make (struct
  type t = DedupId.id

  let equal = DedupId.equal_id
  let hash = Hashtbl.hash
end)

type of_json_ctx = {
  id_to_file_map : file FileTbl.t;
  ty_dedup_tbl : ty DedupTbl.t;
  tref_dedup_tbl : trait_ref DedupTbl.t;
  constant_expr_dedup_tbl : constant_expr DedupTbl.t;
  exact_size_expr_dedup_tbl : exact_size_expr DedupTbl.t;
  span_dedup_tbl : span DedupTbl.t;
}

let empty_of_json_ctx : of_json_ctx =
  {
    id_to_file_map = FileTbl.create 8;
    ty_dedup_tbl = DedupTbl.create 1024;
    tref_dedup_tbl = DedupTbl.create 1024;
    constant_expr_dedup_tbl = DedupTbl.create 1024;
    exact_size_expr_dedup_tbl = DedupTbl.create 1024;
    span_dedup_tbl = DedupTbl.create 4096;
  }

(** Values that come up often are deduplicated in the serialized output: the first
    occurrence of a value is serialized in full along with an id, and later
    occurrences only mention that id. *)
let dedup_val_of_json (tbl : 'a DedupTbl.t)
    (of_json : of_json_ctx -> json -> ('a, string) result) (ctx : of_json_ctx)
    (js : json) : ('a, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Untagged", json) ] -> of_json ctx json
    | `Assoc [ ("Value", `List [ `Int id; json ]) ] ->
        let* v = of_json ctx json in
        DedupTbl.replace tbl (DedupId.of_int id) v;
        Ok v
    | `Assoc [ ("Deduplicated", `Int id) ] -> begin
        match DedupTbl.find_opt tbl (DedupId.of_int id) with
        | Some v -> Ok v
        | None ->
            Error
              "Deduplication key not found; there is a serialization mismatch \
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
