(** WARNING: this file is partially auto-generated. Do not edit `GAst.ml`
    by hand. Edit `GAst.template.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `GAst.template.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

(** Definitions shared between the ULLBC and the LLBC ASTs. *)
open Types

open Meta
open Expressions
module FunDeclId = Expressions.FunDeclId
module GlobalDeclId = Expressions.GlobalDeclId
module TraitDeclId = Types.TraitDeclId
module TraitImplId = Types.TraitImplId
module TraitClauseId = Types.TraitClauseId

(* Imports *)
type builtin_fun_id = Expressions.builtin_fun_id [@@deriving show, ord]
type fun_id = Expressions.fun_id [@@deriving show, ord]
type fun_id_or_trait_method_ref = Expressions.fun_id_or_trait_method_ref [@@deriving show, ord]

(* __REPLACE0__ *)
[@@deriving show, ord]

(* __REPLACE1__ *)

(* __REPLACE2__ *)

(* __REPLACE3__ *)

(* __REPLACE4__ *)

(* __REPLACE5__ *)
[@@deriving show]

(* Hand-written because they don't exist in rust *)
type type_declaration_group = TypeDeclId.id g_declaration_group
[@@deriving show]

type fun_declaration_group = FunDeclId.id g_declaration_group [@@deriving show]

type global_declaration_group = GlobalDeclId.id g_declaration_group
[@@deriving show]

type trait_declaration_group = TraitDeclId.id g_declaration_group
[@@deriving show]

type trait_impl_group = TraitImplId.id g_declaration_group [@@deriving show]
type mixed_declaration_group = any_decl_id g_declaration_group [@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)
type 'body gfun_decl = {
  def_id : FunDeclId.id;
  item_meta : item_meta;
  signature : fun_sig;
  kind : item_kind;
  is_global_initializer: GlobalDeclId.id option;
  body : 'body gexpr_body option;
}
[@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)

(** A crate *)
type 'fun_body gcrate = {
  name : string;
  options : cli_options;
  declarations : declaration_group list;
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : 'fun_body gfun_decl FunDeclId.Map.t;
  global_decls : global_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
}
[@@deriving show]
