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

(* Note: this is duplicated in `Types.ml` but re-exported here to not break dependent projects. *)
type fun_decl_id = FunDeclId.id [@@deriving show, ord]

(* __REPLACE5__ *)
[@@deriving show, ord]

type assumed_fun_id = Expressions.assumed_fun_id [@@deriving show, ord]
type fun_id = Expressions.fun_id [@@deriving show, ord]

type fun_id_or_trait_method_ref = Expressions.fun_id_or_trait_method_ref
[@@deriving show, ord]

(* __REPLACE4__ *)
[@@deriving show]

(** Ancestor the AST iter visitors *)
class ['self] iter_ast_base =
  object (_self : 'self)
    inherit [_] iter_rvalue
    inherit! [_] iter_generic_params
  end

(** Ancestor the AST map visitors *)
class ['self] map_ast_base =
  object (_self : 'self)
    inherit [_] map_rvalue
    inherit! [_] map_generic_params
  end

(* Below: the types need not be mutually recursive, but it makes it easier
   to derive the visitors *)

(** not present in rust *)
type assertion = { cond : operand; expected : bool }

(* __REPLACE0__ *)
[@@deriving
  show,
    visitors
      {
        name = "iter_call";
        variety = "iter";
        ancestors = [ "iter_ast_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_call";
        variety = "map";
        ancestors = [ "map_ast_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor the {!LlbcAst.statement} and {!Charon.UllbcAst.statement} iter visitors *)
class ['self] iter_statement_base =
  object (_self : 'self)
    inherit [_] iter_call
  end

(** Ancestor the {!LlbcAst.statement} and {!Charon.UllbcAst.statement} map visitors *)
class ['self] map_statement_base =
  object (_self : 'self)
    inherit [_] map_call
  end

(* __REPLACE1__ *)
[@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)
type 'body gfun_decl = {
  def_id : FunDeclId.id;
  item_meta : item_meta;
  signature : fun_sig;
  kind : item_kind;
  body : 'body gexpr_body option;
  is_global_decl_body : bool;
}
[@@deriving show]

(* __REPLACE2__ *)
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

(* __REPLACE3__ *)
[@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)
type 'body gglobal_decl = {
  def_id : GlobalDeclId.id;
  item_meta : item_meta;
  generics : generic_params;
  ty : ty;
  kind : item_kind;
  body : 'body;
}
[@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)
(** A crate *)
type ('fun_body, 'global_body) gcrate = {
  name : string;
  declarations : declaration_group list;
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : 'fun_body gfun_decl FunDeclId.Map.t;
  global_decls : 'global_body gglobal_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
}
[@@deriving show]
