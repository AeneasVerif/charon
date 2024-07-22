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

type __5 = unit (* to start the recursive group *)

and any_decl_id =
  | IdType of type_decl_id
  | IdFun of fun_decl_id
  | IdGlobal of global_decl_id
  | IdTraitDecl of trait_decl_id
  | IdTraitImpl of trait_impl_id
[@@deriving show, ord]

type assumed_fun_id = Expressions.assumed_fun_id [@@deriving show, ord]
type fun_id = Expressions.fun_id [@@deriving show, ord]

type fun_id_or_trait_method_ref = Expressions.fun_id_or_trait_method_ref
[@@deriving show, ord]

type __4 = unit (* to start the recursive group *)

and var = { index : var_id; name : string option; var_ty : ty }
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
type __0 = unit (* to start the recursive group *)
and assertion = { cond : operand; expected : bool }

(* not present in rust *)
and fn_operand = FnOpRegular of fn_ptr | FnOpMove of place

and call = { func : fn_operand; args : operand list; dest : place }
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

type __1 = unit (* to start the recursive group *)

and params_info = {
  num_region_params : int;
  num_type_params : int;
  num_const_generic_params : int;
  num_trait_clauses : int;
  num_regions_outlive : int;
  num_types_outlive : int;
  num_trait_type_constraints : int;
}

and closure_kind = Fn | FnMut | FnOnce
and closure_info = { kind : closure_kind; state : ty list }

and fun_sig = {
  is_unsafe : bool;
  is_closure : bool;
  closure_info : closure_info option;
  generics : generic_params;
  parent_params_info : params_info option;
  inputs : ty list;
  output : ty;
}

and item_kind =
  | RegularKind
  | TraitItemImpl of trait_impl_id * trait_decl_id * trait_item_name * bool
  | TraitItemDecl of trait_decl_id * trait_item_name
  | TraitItemProvided of trait_decl_id * trait_item_name

and 'a0 gexpr_body = {
  span : span;
  arg_count : int;
  locals : var list;
  body : 'a0;
}
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

type __2 = unit (* to start the recursive group *)

and trait_decl = {
  def_id : trait_decl_id;
  item_meta : item_meta;
  generics : generic_params;
  parent_clauses : trait_clause list;
  consts : (trait_item_name * ty) list;
  types : trait_item_name list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id option) list;
}

and trait_impl = {
  def_id : trait_impl_id;
  item_meta : item_meta;
  impl_trait : trait_decl_ref;
  generics : generic_params;
  parent_trait_refs : trait_ref list;
  consts : (trait_item_name * global_decl_ref) list;
  types : (trait_item_name * ty) list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id) list;
}

and 'a0 g_declaration_group = NonRecGroup of 'a0 | RecGroup of 'a0 list
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

type __3 = unit (* to start the recursive group *)

and declaration_group =
  | TypeGroup of type_decl_id g_declaration_group
  | FunGroup of fun_decl_id g_declaration_group
  | GlobalGroup of global_decl_id g_declaration_group
  | TraitDeclGroup of trait_decl_id g_declaration_group
  | TraitImplGroup of trait_impl_id g_declaration_group
  | MixedGroup of any_decl_id g_declaration_group
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
