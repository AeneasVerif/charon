include GAst
open Types
open Values
open Expressions
open Meta
open Identifiers
module BlockId = IdGen ()

(** We define this type to control the name of the visitor functions
    (see e.g., {!UllbcAst.iter_statement_base} and {!switch}).
  *)
type block_id = BlockId.id [@@deriving show, ord]

(* __REPLACE0__ *)

(* __REPLACE1__ *)

type expr_body = blocks gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = blocks gfun_decl [@@deriving show]

(** ULLBC crate *)
type crate = blocks gcrate
