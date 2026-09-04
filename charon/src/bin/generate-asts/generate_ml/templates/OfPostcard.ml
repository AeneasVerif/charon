(** WARNING: this file is partially auto-generated. Do not edit `OfPostcard.ml`
    by hand. Edit `generate_ml/templates/OfPostcard.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/OfPostcard.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`.
 *)

open OfPostcardBasic
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

type of_postcard_ctx = {
  id_to_file_map : file FileTbl.t;
  ty_dedup_tbl : ty DedupTbl.t;
  tref_dedup_tbl : trait_ref DedupTbl.t;
  constant_expr_dedup_tbl : constant_expr DedupTbl.t;
  exact_size_expr_dedup_tbl : exact_size_expr DedupTbl.t;
  span_dedup_tbl : span DedupTbl.t;
}

let empty_of_postcard_ctx : of_postcard_ctx =
  {
    id_to_file_map = FileTbl.create 8;
    ty_dedup_tbl = DedupTbl.create 2048;
    tref_dedup_tbl = DedupTbl.create 1024;
    constant_expr_dedup_tbl = DedupTbl.create 64;
    exact_size_expr_dedup_tbl = DedupTbl.create 16;
    span_dedup_tbl = DedupTbl.create 4096;
  }

(** Values that come up often are deduplicated in the serialized output: the first
    occurrence of a value is serialized in full along with an id, and later
    occurrences only mention that id. *)
let dedup_val_of_postcard (tbl : 'a DedupTbl.t)
    (of_postcard : of_postcard_ctx -> postcard_state -> ('a, string) result)
    (ctx : of_postcard_ctx) (st : postcard_state) : ('a, string) result =
  combine_error_msgs st __FUNCTION__
    (let* tag = int_of_postcard ctx st in
     match tag with
     | 0 ->
         let* id = DedupId.id_of_postcard ctx st in
         let* v = of_postcard ctx st in
         DedupTbl.replace tbl id v;
         Ok v
     | 1 ->
         let* id = DedupId.id_of_postcard ctx st in
         begin
           match DedupTbl.find_opt tbl id with
           | Some v -> Ok v
           | None ->
               Error
                 "Deduplication key not found; there is a serialization mismatch \
                  between Rust and OCaml"
         end
     | 2 -> of_postcard ctx st
     | _ -> Error "invalid deduplicated value representation")

let path_buf_of_postcard = string_of_postcard

let opt_indexed_map_of_postcard :
    'a0 'a1.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a1, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a1 option list, string) result =
 fun arg0_of_postcard arg1_of_postcard ctx st ->
  list_of_postcard (option_of_postcard arg1_of_postcard) ctx st

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
