open Identifiers
open Generated_Meta
open Generated_Types
module FileId = IdGen ()
module DedupId = IdGen ()

module FileTbl = Hashtbl.Make (struct
  type t = FileId.id

  let equal = FileId.equal_id
  let hash = Hashtbl.hash
end)

(** Table of the values that were deduplicated in the serialized output, by id.
*)
module DedupTbl = Hashtbl.Make (struct
  type t = DedupId.id

  let equal = DedupId.equal_id
  let hash = Hashtbl.hash
end)

type t = {
  id_to_file_map : file FileTbl.t;
  ty_dedup_tbl : ty DedupTbl.t;
  tref_dedup_tbl : trait_ref DedupTbl.t;
  constant_expr_dedup_tbl : constant_expr DedupTbl.t;
  size_expr_dedup_tbl : size_expr DedupTbl.t;
  inhabited_predicate_dedup_tbl : inhabited_predicate DedupTbl.t;
  span_dedup_tbl : span DedupTbl.t;
}

let empty () : t =
  {
    id_to_file_map = FileTbl.create 8;
    ty_dedup_tbl = DedupTbl.create 2048;
    tref_dedup_tbl = DedupTbl.create 1024;
    constant_expr_dedup_tbl = DedupTbl.create 64;
    size_expr_dedup_tbl = DedupTbl.create 16;
    inhabited_predicate_dedup_tbl = DedupTbl.create 16;
    span_dedup_tbl = DedupTbl.create 4096;
  }
