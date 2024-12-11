
(** WARNING: this file is partially auto-generated. Do not edit `Types.ml`
    by hand. Edit `Types.template.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `Types.template.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

open Identifiers
open Meta
open Values
module TypeVarId = IdGen ()
module TypeDeclId = IdGen ()
module VariantId = IdGen ()
module FieldId = IdGen ()
module GlobalDeclId = IdGen ()
module ConstGenericVarId = IdGen ()
module TraitDeclId = IdGen ()
module TraitImplId = IdGen ()
module TraitClauseId = IdGen ()
module UnsolvedTraitId = IdGen ()
module BoundRegionId = IdGen ()
module FreeRegionId = IdGen ()
module RegionGroupId = IdGen ()
module Disambiguator = IdGen ()
module FunDeclId = IdGen ()
module BodyId = IdGen ()

type ('a, 'b) outlives_pred = 'a * 'b [@@deriving show, ord]
type ('id, 'x) vector = 'x list [@@deriving show, ord]

type integer_type = Values.integer_type [@@deriving show, ord]
type float_type = Values.float_type [@@deriving show, ord]
type literal_type = Values.literal_type [@@deriving show, ord]

(** We define these types to control the name of the visitor functions
    (see e.g., {!class:Types.iter_ty_base} and {!Types.TVar}).
  *)
type bound_region_id = BoundRegionId.id [@@deriving show, ord]
type free_region_id = FreeRegionId.id [@@deriving show, ord]
type region_group_id = RegionGroupId.id [@@deriving show, ord]

type ('id, 'name) indexed_var = {
  index : 'id;  (** Unique index identifying the variable *)
  name : 'name;  (** Variable name *)
}
[@@deriving show, ord]

(* __REPLACE0__ *)
[@@deriving show, ord]

let all_signed_int_types = [ Isize; I8; I16; I32; I64; I128 ]
let all_unsigned_int_types = [ Usize; U8; U16; U32; U64; U128 ]
let all_int_types = List.append all_signed_int_types all_unsigned_int_types

(** The variant id for [Option::None] *)
let option_none_id = VariantId.of_int 0

(** The variant id for [Option::Some] *)
let option_some_id = VariantId.of_int 1

class ['self] iter_const_generic_base_base =
  object (self : 'self)
    inherit [_] iter_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> unit = fun _ _ -> ()

    method visit_de_bruijn_var
        : 'b 'f.
          ('env -> 'b -> unit) ->
          ('env -> 'f -> unit) ->
          'env ->
          ('b, 'f) de_bruijn_var ->
          unit =
      fun visit_bound visit_free env x ->
        match x with
        | Bound (dbid, varid) ->
            self#visit_de_bruijn_id env dbid;
            visit_bound env varid
        | Free varid -> visit_free env varid
  end

(** Ancestor for map visitor for {!type: Types.ty} *)
class virtual ['self] map_const_generic_base_base =
  object (self : 'self)
    inherit [_] map_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> de_bruijn_id =
      fun _ x -> x

    method visit_de_bruijn_var
        : 'b 'f.
          ('env -> 'b -> 'b) ->
          ('env -> 'f -> 'f) ->
          'env ->
          ('b, 'f) de_bruijn_var ->
          ('b, 'f) de_bruijn_var =
      fun visit_bound visit_free env x ->
        match x with
        | Bound (dbid, varid) ->
            let dbid = self#visit_de_bruijn_id env dbid in
            let varid = visit_bound env varid in
            Bound (dbid, varid)
        | Free varid ->
            let varid = visit_free env varid in
            Free varid
  end

class virtual ['self] reduce_const_generic_base_base =
  object (self : 'self)
    inherit [_] reduce_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> 'a =
      fun _ _ -> self#zero

    method visit_de_bruijn_var
        : 'b 'f.
          ('env -> 'b -> 'a) ->
          ('env -> 'f -> 'a) ->
          'env ->
          ('b, 'f) de_bruijn_var ->
          'a =
      fun visit_bound visit_free env x ->
        match x with
        | Bound (dbid, varid) ->
            let acc1 = self#visit_de_bruijn_id env dbid in
            let acc2 = visit_bound env varid in
            self#plus acc1 acc2
        | Free varid ->
            let acc = visit_free env varid in
            acc
  end

class virtual ['self] mapreduce_const_generic_base_base =
  object (self : 'self)
    inherit [_] mapreduce_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> de_bruijn_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_de_bruijn_var
        : 'b 'f.
          ('env -> 'b -> 'b * 'a) ->
          ('env -> 'f -> 'f * 'a) ->
          'env ->
          ('b, 'f) de_bruijn_var ->
          ('b, 'f) de_bruijn_var * 'a =
      fun visit_bound visit_free env x ->
        match x with
        | Bound (dbid, varid) ->
            let dbid, acc1 = self#visit_de_bruijn_id env dbid in
            let varid, acc2 = visit_bound env varid in
            (Bound (dbid, varid), self#plus acc1 acc2)
        | Free varid ->
            let varid, acc = visit_free env varid in
            (Free varid, acc)
  end

(* __REPLACE1__ *)

(** Region variable. *)
type region_var = (bound_region_id, string option) indexed_var
[@@deriving show, ord]

(** A value of type `'a` bound by generic parameters. *)
type 'a region_binder = { binder_regions : region_var list; binder_value : 'a }
[@@deriving show, ord]

(** Ancestor for iter visitor for {!type: Types.ty} *)
class ['self] iter_ty_base_base =
  object (self : 'self)
    inherit [_] iter_const_generic

    method visit_indexed_var
        : 'id 'name.
          ('env -> 'id -> unit) ->
          ('env -> 'name -> unit) ->
          'env ->
          ('id, 'name) indexed_var ->
          unit =
      fun visit_index visit_name env x ->
        let { index; name } = x in
        visit_index env index;
        visit_name env name

    method visit_outlives_pred
        : 'l 'r.
          ('env -> 'l -> unit) ->
          ('env -> 'r -> unit) ->
          'env ->
          ('l, 'r) outlives_pred ->
          unit =
      fun visit_left visit_right env x ->
        let left, right = x in
        visit_left env left;
        visit_right env right

    method visit_region_var env (x : region_var) =
      self#visit_indexed_var self#visit_bound_region_id
        (self#visit_option self#visit_string)
        env x

    method visit_region_binder
        : 'a. ('env -> 'a -> unit) -> 'env -> 'a region_binder -> unit =
      fun visit_binder_value env x ->
        let { binder_regions; binder_value } = x in
        self#visit_list self#visit_region_var env binder_regions;
        visit_binder_value env binder_value
  end

(** Ancestor for map visitor for {!type: Types.ty} *)
class virtual ['self] map_ty_base_base =
  object (self : 'self)
    inherit [_] map_const_generic

    method visit_indexed_var
        : 'id 'name.
          ('env -> 'id -> 'id) ->
          ('env -> 'name -> 'name) ->
          'env ->
          ('id, 'name) indexed_var ->
          ('id, 'name) indexed_var =
      fun visit_index visit_name env x ->
        let { index; name } = x in
        let index = visit_index env index in
        let name = visit_name env name in
        { index; name }

    method visit_outlives_pred
        : 'l 'r.
          ('env -> 'l -> 'l) ->
          ('env -> 'r -> 'r) ->
          'env ->
          ('l, 'r) outlives_pred ->
          ('l, 'r) outlives_pred =
      fun visit_left visit_right env x ->
        let left, right = x in
        let left = visit_left env left in
        let right = visit_right env right in
        (left, right)

    method visit_region_var env (x : region_var) =
      self#visit_indexed_var self#visit_bound_region_id
        (self#visit_option self#visit_string)
        env x

    method visit_region_binder
        : 'a. ('env -> 'a -> 'a) -> 'env -> 'a region_binder -> 'a region_binder
        =
      fun visit_binder_value env x ->
        let { binder_regions; binder_value } = x in
        let binder_regions = self#visit_list self#visit_region_var env binder_regions in
        let binder_value = visit_binder_value env binder_value in
        { binder_regions; binder_value }
  end

(* __REPLACE2__ *)

(* __REPLACE3__ *)

(* __REPLACE4__ *)
[@@deriving show, ord]

(* __REPLACE5__ *)

(** A group of regions.

    Results from a lifetime analysis: we group the regions with the same
    lifetime together, and compute the hierarchy between the regions.
    This is necessary to introduce the proper abstraction with the
    proper constraints, when evaluating a function call in symbolic mode.
*)
(* Hand-written because these don't exist on the rust side *)
type ('rid, 'id) g_region_group = {
  id : 'id;
  regions : 'rid list;
  parents : 'id list;
}
[@@deriving show]

type region_db_var = (bound_region_id, free_region_id) de_bruijn_var [@@deriving show]
type type_db_var = (type_var_id, type_var_id) de_bruijn_var [@@deriving show]
type const_generic_db_var = (const_generic_var_id, const_generic_var_id) de_bruijn_var [@@deriving show]
type trait_db_var = (trait_clause_id, trait_clause_id) de_bruijn_var [@@deriving show]

type region_var_group = (BoundRegionId.id, RegionGroupId.id) g_region_group
[@@deriving show]

type region_var_groups = region_var_group list [@@deriving show]

(** Type with erased regions (this only has an informative purpose) *)
type ety = ty

(** Type with non-erased regions (this only has an informative purpose) *)
and rty = ty
[@@deriving show, ord]
