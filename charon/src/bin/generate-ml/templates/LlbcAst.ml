include GAst
open Types
open Values
open Expressions
open Meta

(* __REPLACE0__ *)

type expr_body = statement gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = statement gfun_decl [@@deriving show]

(** LLBC crate *)
type crate = statement gcrate
