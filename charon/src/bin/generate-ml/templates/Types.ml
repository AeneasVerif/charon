
(** WARNING: this file is partially auto-generated. Do not edit `Types.ml`
    by hand. Edit `Types.template.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `Types.template.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

open Identifiers
open Generated_Meta
open Generated_Values

module TypeVarId = IdGen ()
module TypeDeclId = IdGen ()
module VariantId = IdGen ()
module FieldId = IdGen ()
module GlobalDeclId = IdGen ()
module ConstGenericVarId = IdGen ()
module TraitDeclId = IdGen ()
module TraitImplId = IdGen ()
module TraitMethodId = IdGen ()
module AssocTypeId = IdGen ()
module AssocConstId = IdGen ()
module TraitClauseId = IdGen ()
module TraitTypeConstraintId = IdGen ()
module UnsolvedTraitId = IdGen ()
module RegionId = IdGen ()
module Disambiguator = IdGen ()
module FunDeclId = IdGen ()

type integer_type = Values.integer_type [@@deriving show, ord, eq]
type float_type = Values.float_type [@@deriving show, ord, eq]
type literal_type = Values.literal_type [@@deriving show, ord, eq]

(* Manually implemented because no type uses it (we use plain lists instead of
   vectors in generic_params), which causes visitor inference problems if we
   declare it within a visitor group. *)
type trait_type_constraint_id = TraitTypeConstraintId.id [@@deriving show, ord, eq]

type 'a fun_decl_id_map = 'a FunDeclId.Map.t
and 'a global_decl_id_map = 'a GlobalDeclId.Map.t
and 'a type_decl_id_map = 'a TypeDeclId.Map.t
and 'a trait_decl_id_map = 'a TraitDeclId.Map.t
and 'a trait_impl_id_map = 'a TraitImplId.Map.t
and 'a trait_method_id_map = 'a TraitMethodId.Map.t
and 'a assoc_type_id_map = 'a AssocTypeId.Map.t [@@deriving show, eq, ord]


(* __REPLACE0__ *)

class ['self] iter_ty_base =
  object (self : 'self)
    inherit [_] iter_type_vars
    method visit_span : 'env -> span -> unit = fun _ _ -> ()
    method visit_assoc_type_id_map
        : 'a. ('env -> 'a -> unit) -> 'env -> 'a assoc_type_id_map -> unit =
      AssocTypeId.Map.visit_iter
  end

class ['self] map_ty_base =
  object (self : 'self)
    inherit [_] map_type_vars
    method visit_span : 'env -> span -> span = fun _ x -> x
    method visit_assoc_type_id_map
        : 'a 'b. ('env -> 'a -> 'b) -> 'env -> 'a assoc_type_id_map -> 'b assoc_type_id_map =
      AssocTypeId.Map.visit_map
  end

(* __REPLACE1__ *)

(* __REPLACE2__ *)
