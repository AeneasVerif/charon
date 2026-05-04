(** Definitions shared between the ULLBC and the LLBC ASTs. *)
open Types

open Meta
open Expressions
include Generated_GAst
include Generated_FullAst

(* FIXME(#287): Avoid derives triggering deprecation warnings *)
[@@@alert "-deprecated"]

type var = local
[@@ocaml.deprecated "use [local] instead"] [@@deriving show, eq, ord]

(* Hand-written because they don't exist in rust *)
type type_declaration_group = TypeDeclId.id g_declaration_group
[@@deriving show]

type fun_declaration_group = FunDeclId.id g_declaration_group [@@deriving show]

type global_declaration_group = GlobalDeclId.id g_declaration_group
[@@deriving show]

type trait_declaration_group = TraitDeclId.id g_declaration_group
[@@deriving show]

type trait_impl_group = TraitImplId.id g_declaration_group [@@deriving show]
type mixed_declaration_group = item_id g_declaration_group [@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)

(** A crate *)
type crate = {
  name : string;
  options : cli_options;
  target_information : (string * target_info) list;
  declarations : declaration_group list;
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : fun_decl FunDeclId.Map.t;
  global_decls : global_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
  unit_metadata : global_decl_ref;
}
[@@deriving show]
