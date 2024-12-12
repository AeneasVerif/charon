
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
module RegionId = IdGen ()
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
type region_id = RegionId.id [@@deriving show, ord]

type ('id, 'name) indexed_var = {
  index : 'id;  (** Unique index identifying the variable *)
  name : 'name;  (** Variable name *)
}
[@@deriving show, ord]

(* __REPLACE0__ *)
[@@deriving show, ord]

class ['self] iter_const_generic_base_base =
  object (self : 'self)
    inherit [_] iter_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> unit = fun _ _ -> ()

    method visit_de_bruijn_var
        : 'id.
          ('env -> 'id -> unit) ->
          'env ->
          'id de_bruijn_var ->
          unit =
      fun visit_id env x ->
        match x with
        | Bound (dbid, varid) ->
            self#visit_de_bruijn_id env dbid;
            visit_id env varid
        | Free varid -> visit_id env varid
  end

(** Ancestor for map visitor for {!type: Types.ty} *)
class virtual ['self] map_const_generic_base_base =
  object (self : 'self)
    inherit [_] map_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> de_bruijn_id =
      fun _ x -> x

    method visit_de_bruijn_var
        : 'id 'f.
          ('env -> 'id -> 'id) ->
          'env ->
          'id de_bruijn_var ->
          'id de_bruijn_var =
      fun visit_id env x ->
        match x with
        | Bound (dbid, varid) ->
            let dbid = self#visit_de_bruijn_id env dbid in
            let varid = visit_id env varid in
            Bound (dbid, varid)
        | Free varid ->
            let varid = visit_id env varid in
            Free varid
  end

class virtual ['self] reduce_const_generic_base_base =
  object (self : 'self)
    inherit [_] reduce_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> 'a =
      fun _ _ -> self#zero

    method visit_de_bruijn_var
        : 'id 'f.
          ('env -> 'id -> 'a) ->
          'env ->
          'id de_bruijn_var ->
          'a =
      fun visit_id env x ->
        match x with
        | Bound (dbid, varid) ->
            let acc1 = self#visit_de_bruijn_id env dbid in
            let acc2 = visit_id env varid in
            self#plus acc1 acc2
        | Free varid ->
            let acc = visit_id env varid in
            acc
  end

class virtual ['self] mapreduce_const_generic_base_base =
  object (self : 'self)
    inherit [_] mapreduce_literal

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> de_bruijn_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_de_bruijn_var
        : 'id 'f.
          ('env -> 'id -> 'id * 'a) ->
          'env ->
          'id de_bruijn_var ->
          'id de_bruijn_var * 'a =
      fun visit_id env x ->
        match x with
        | Bound (dbid, varid) ->
            let dbid, acc1 = self#visit_de_bruijn_id env dbid in
            let varid, acc2 = visit_id env varid in
            (Bound (dbid, varid), self#plus acc1 acc2)
        | Free varid ->
            let varid, acc = visit_id env varid in
            (Free varid, acc)
  end

(* __REPLACE1__ *)

(** Region variable. *)
type region_var = (region_id, string option) indexed_var
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
      self#visit_indexed_var self#visit_region_id
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
      self#visit_indexed_var self#visit_region_id
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
