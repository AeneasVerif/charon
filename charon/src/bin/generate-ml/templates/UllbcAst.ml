open Types
open Values
open Expressions
open Meta
open Identifiers
open GAst

module BlockId = IdGen ()

(** We define this type to control the name of the visitor functions
    (see e.g., {!UllbcAst.iter_statement_base} and {!switch}).
  *)
type block_id = BlockId.id [@@deriving show, ord]

(* __REPLACE0__ *)

(* __REPLACE1__ *)
