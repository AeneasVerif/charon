(** WARNING: this file is partially auto-generated. Do not edit `src/Meta.ml`
    by hand. Edit `generate_ml/templates/Meta.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/Meta.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`.
 *)

open Identifiers

module TypeDeclId = IdGen ()
module GlobalDeclId = IdGen ()
module TraitDeclId = IdGen ()
module TraitImplId = IdGen ()
module FunDeclId = IdGen ()
module TraitMethodId = IdGen ()
module AssocTypeId = IdGen ()
module AssocConstId = IdGen ()

type path_buf = string
[@@deriving show, ord, eq]

(* __REPLACE0__ *)
