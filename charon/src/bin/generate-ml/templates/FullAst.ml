(** WARNING: this file is partially auto-generated. Do not edit `FullAst.ml`
    by hand. Edit `templates/FullAst.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templates/FullAst.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

 open Generated_GAst
 open Generated_UllbcAst
 open Generated_LlbcAst
 open Types
 open Values
 open Expressions
 open Meta
 open Identifiers

 (* __REPLACE0__ *)
 [@@deriving show]
