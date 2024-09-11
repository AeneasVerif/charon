(** WARNING: this file is partially auto-generated. Do not edit `src/Expressions.ml`
    by hand. Edit `templates/Expressions.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templates/Expressions.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)
open Identifiers
open Types
open Values
module VarId = IdGen ()
module GlobalDeclId = Types.GlobalDeclId
module FunDeclId = Types.FunDeclId

(* __REPLACE0__ *)
[@@deriving show, ord]

(* __REPLACE1__ *)

(* __REPLACE2__ *)
[@@deriving show, ord]

let all_binops =
  [
    BitXor;
    BitAnd;
    BitOr;
    Eq;
    Lt;
    Le;
    Ne;
    Ge;
    Gt;
    Div;
    Rem;
    Add;
    Sub;
    Mul;
    Shl;
    Shr;
  ]

(* __REPLACE3__ *)

(* __REPLACE4__ *)
