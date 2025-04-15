open Types
open Values
open Expressions
open Meta
include GAst
include Generated_LlbcAst

type expr_body = block gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = block gfun_decl [@@deriving show]

(** LLBC crate *)
type crate = block gcrate [@@deriving show]
