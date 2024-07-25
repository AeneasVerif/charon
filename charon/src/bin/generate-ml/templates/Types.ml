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
module RegionVarId = IdGen ()
module RegionId = IdGen ()
module RegionGroupId = IdGen ()
module Disambiguator = IdGen ()
module FunDeclId = IdGen ()
module BodyId = IdGen ()

type ('a, 'b) outlives_pred = 'a * 'b
type ('id, 'x) vector = 'x list [@@deriving show, ord]

(** We define this type to control the name of the visitor functions
    (see e.g., {!class:Types.iter_ty_base} and {!Types.TVar}).
  *)
type type_var_id = TypeVarId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type const_generic_var_id = ConstGenericVarId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type global_decl_id = GlobalDeclId.id [@@deriving show, ord]

type integer_type = Values.integer_type [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type variant_id = VariantId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type field_id = FieldId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type type_decl_id = TypeDeclId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type fun_decl_id = FunDeclId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type trait_decl_id = TraitDeclId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type trait_impl_id = TraitImplId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type trait_clause_id = TraitClauseId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type region_var_id = RegionVarId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type region_id = RegionId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type region_group_id = RegionGroupId.id [@@deriving show, ord]

type disambiguator = Disambiguator.id [@@deriving show, ord]

(** Region DeBruijn identifiers *)
type region_db_id = int [@@deriving show, ord]

type ('id, 'name) indexed_var = {
  index : 'id;  (** Unique index identifying the variable *)
  name : 'name;  (** Variable name *)
}
[@@deriving show, ord]

type type_var = (TypeVarId.id, string) indexed_var [@@deriving show, ord]

type region_var = (RegionVarId.id, string option) indexed_var
[@@deriving show, ord]

type literal_type = Values.literal_type [@@deriving show, ord]

type const_generic_var = {
  index : ConstGenericVarId.id;
  name : string;
  ty : literal_type;
}
[@@deriving show, ord]

let all_signed_int_types = [ Isize; I8; I16; I32; I64; I128 ]
let all_unsigned_int_types = [ Usize; U8; U16; U32; U64; U128 ]
let all_int_types = List.append all_signed_int_types all_unsigned_int_types

type ref_kind = RMut | RShared [@@deriving show, ord]

(** The variant id for [Option::None] *)
let option_none_id = VariantId.of_int 0

(** The variant id for [Option::Some] *)
let option_some_id = VariantId.of_int 1

(** Ancestor for iter visitor for {!Types.const_generic} *)
class ['self] iter_const_generic_base =
  object (_self : 'self)
    inherit [_] iter_literal
    method visit_type_decl_id : 'env -> type_decl_id -> unit = fun _ _ -> ()
    method visit_global_decl_id : 'env -> global_decl_id -> unit = fun _ _ -> ()

    method visit_const_generic_var_id : 'env -> const_generic_var_id -> unit =
      fun _ _ -> ()
  end

(** Ancestor for map visitor for {!Types.const_generic} *)
class ['self] map_const_generic_base =
  object (_self : 'self)
    inherit [_] map_literal

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id =
      fun _ x -> x

    method visit_global_decl_id : 'env -> global_decl_id -> global_decl_id =
      fun _ x -> x

    method visit_const_generic_var_id
        : 'env -> const_generic_var_id -> const_generic_var_id =
      fun _ x -> x
  end

(** Ancestor for reduce visitor for {!Types.const_generic} *)
class virtual ['self] reduce_const_generic_base =
  object (self : 'self)
    inherit [_] reduce_literal

    method visit_type_decl_id : 'env -> type_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_global_decl_id : 'env -> global_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_const_generic_var_id : 'env -> const_generic_var_id -> 'a =
      fun _ _ -> self#zero
  end

(** Ancestor for mapreduce visitor for {!Types.const_generic} *)
class virtual ['self] mapreduce_const_generic_base =
  object (self : 'self)
    inherit [_] mapreduce_literal

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_global_decl_id : 'env -> global_decl_id -> global_decl_id * 'a
        =
      fun _ x -> (x, self#zero)

    method visit_const_generic_var_id
        : 'env -> const_generic_var_id -> const_generic_var_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** Remark: we have to use long names because otherwise we have collisions in
    the functions derived for the visitors. *)
type const_generic =
  | CgGlobal of global_decl_id
  | CgVar of const_generic_var_id
  | CgValue of literal
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_const_generic";
        variety = "iter";
        ancestors = [ "iter_const_generic_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_const_generic";
        variety = "map";
        ancestors = [ "map_const_generic_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.map} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "reduce_const_generic";
        variety = "reduce";
        ancestors = [ "reduce_const_generic_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.reduce} *);
        polymorphic = false;
      },
    visitors
      {
        name = "mapreduce_const_generic";
        variety = "mapreduce";
        ancestors = [ "mapreduce_const_generic_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.mapreduce} *);
        polymorphic = false;
      }]

type trait_item_name = string [@@deriving show, ord]

(** Ancestor for iter visitor for {!type: Types.ty} *)
class ['self] iter_ty_base =
  object (self : 'self)
    inherit [_] iter_const_generic
    method visit_region_db_id : 'env -> region_db_id -> unit = fun _ _ -> ()
    method visit_region_var_id : 'env -> region_var_id -> unit = fun _ _ -> ()
    method visit_region_id : 'env -> region_id -> unit = fun _ _ -> ()
    method visit_type_var_id : 'env -> type_var_id -> unit = fun _ _ -> ()
    method visit_ref_kind : 'env -> ref_kind -> unit = fun _ _ -> ()

    method visit_trait_item_name : 'env -> trait_item_name -> unit =
      fun _ _ -> ()

    method visit_fun_decl_id : 'env -> fun_decl_id -> unit = fun _ _ -> ()
    method visit_trait_decl_id : 'env -> trait_decl_id -> unit = fun _ _ -> ()
    method visit_trait_impl_id : 'env -> trait_impl_id -> unit = fun _ _ -> ()

    method visit_trait_clause_id : 'env -> trait_clause_id -> unit =
      fun _ _ -> ()

    method visit_region_var : 'env -> region_var -> unit =
      fun env x ->
        let { index; name } : region_var = x in
        self#visit_region_var_id env index;
        self#visit_option self#visit_string env name
  end

(** Ancestor for map visitor for {!type: Types.ty} *)
class virtual ['self] map_ty_base =
  object (self : 'self)
    inherit [_] map_const_generic

    method visit_region_db_id : 'env -> region_db_id -> region_db_id =
      fun _ id -> id

    method visit_region_var_id : 'env -> region_var_id -> region_var_id =
      fun _ id -> id

    method visit_region_id : 'env -> region_id -> region_id = fun _ id -> id

    method visit_type_var_id : 'env -> type_var_id -> type_var_id =
      fun _ id -> id

    method visit_ref_kind : 'env -> ref_kind -> ref_kind = fun _ rk -> rk

    method visit_trait_item_name : 'env -> trait_item_name -> trait_item_name =
      fun _ x -> x

    method visit_fun_decl_id : 'env -> fun_decl_id -> fun_decl_id = fun _ x -> x

    method visit_trait_decl_id : 'env -> trait_decl_id -> trait_decl_id =
      fun _ x -> x

    method visit_trait_impl_id : 'env -> trait_impl_id -> trait_impl_id =
      fun _ x -> x

    method visit_trait_clause_id : 'env -> trait_clause_id -> trait_clause_id =
      fun _ x -> x

    method visit_region_var : 'env -> region_var -> region_var =
      fun env x ->
        let { index; name } : region_var = x in
        let index = self#visit_region_var_id env index in
        let name = self#visit_option self#visit_string env name in
        { index; name }
  end

type __types_0 = unit (* to start the recursive group *)
(* __REPLACE0__ *)

(* Hand-written because we add an extra variant not present on the rust side *)
and trait_instance_id =
  | Self
      (** Reference to *self*, in case of trait declarations/implementations *)
  | TraitImpl of trait_impl_id * generic_args  (** A specific implementation *)
  | BuiltinOrAuto of trait_decl_ref
  | Clause of trait_clause_id
  | ParentClause of trait_instance_id * trait_decl_id * trait_clause_id
  | FnPointer of ty
  | Closure of fun_decl_id * generic_args
  | Dyn of trait_decl_ref
  | Unsolved of trait_decl_id * generic_args
  | UnknownTrait of string
      (** Not present in the Rust version of Charon.

          We use this in the substitutions, to substitute [Self] when [Self] shouldn't
          appear: this allows us to track errors by making sure [Self] indeed did not
          appear.
       *)

(** A region.

    This definition doesn't need to be mutually recursive with the others, but
    this allows us to factor out the visitors.
 *)
(* Hand-written because we add an extra variant not present on the rust side *)
and region =
  | RStatic  (** Static region *)
  | RBVar of region_db_id * region_var_id
      (** Bound region. We use those in function signatures, type definitions, etc. *)
  | RFVar of region_id
      (** Free region. We use those during the symbolic execution. *)
  | RErased  (** Erased region *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_ty";
        variety = "iter";
        ancestors = [ "iter_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "map_ty_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.map} *);
        concrete = false;
        polymorphic = false;
      }]

(** Ancestor for iter visitor for {!type: Types.generic_params} *)
class ['self] iter_generic_params_base =
  object (self : 'self)
    inherit [_] iter_ty
    method visit_span : 'env -> span -> unit = fun _ _ -> ()

    method visit_type_var : 'env -> type_var -> unit =
      fun env x ->
        let { index; name } : type_var = x in
        self#visit_type_var_id env index;
        self#visit_string env name

    method visit_const_generic_var : 'env -> const_generic_var -> unit =
      fun env x ->
        let { index; name; ty } : const_generic_var = x in
        self#visit_const_generic_var_id env index;
        self#visit_string env name;
        self#visit_literal_type env ty
  end

(** Ancestor for map visitor for {!type: Types.generic_params} *)
class virtual ['self] map_generic_params_base =
  object (self : 'self)
    inherit [_] map_ty
    method visit_span : 'env -> span -> span = fun _ x -> x

    method visit_type_var : 'env -> type_var -> type_var =
      fun env x ->
        let { index; name } : type_var = x in
        let index = self#visit_type_var_id env index in
        let name = self#visit_string env name in
        { index; name }

    method visit_const_generic_var
        : 'env -> const_generic_var -> const_generic_var =
      fun env x ->
        let { index; name; ty } : const_generic_var = x in
        let index = self#visit_const_generic_var_id env index in
        let name = self#visit_string env name in
        let ty = self#visit_literal_type env ty in
        { index; name; ty }
  end

(** Type with erased regions (this only has an informative purpose) *)
type ety = ty

(** Type with non-erased regions (this only has an informative purpose) *)
and rty = ty

(* __REPLACE1__ *)

(* Hand-written because visitors can't handle `outlives_pred` *)
and generic_params = {
  regions : region_var list;
  types : type_var list;
      (** The type parameters can be indexed with {!Types.TypeVarId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  const_generics : const_generic_var list;
      (** The const generic parameters can be indexed with {!Types.ConstGenericVarId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  trait_clauses : trait_clause list;
      (** **REMARK:**:
          The indices used by the trait clauses may not be contiguous
          (e.g., we may have the list: `[clause 0; clause 2; clause3; clause 5]`).
          because of the way the clauses are resolved in hax (see the comments
          in Charon).
        *)
  regions_outlive : region_outlives list;
  types_outlive : type_outlives list;
  trait_type_constraints : trait_type_constraint list;
}

(** ('long, 'short) means that 'long outlives 'short *)
and region_outlives = region * region

(** (T, 'a) means that T outlives 'a *)
and type_outlives = ty * region

(* __REPLACE2__ *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_generic_params";
        variety = "iter";
        ancestors = [ "iter_generic_params_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_generic_params";
        variety = "map";
        ancestors = [ "map_generic_params_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.map} *);
        concrete = false;
        polymorphic = false;
      }]

type __types_3 = unit (* to start the recursive group *)
(* __REPLACE3__ *)
[@@deriving show, ord]

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

type region_var_group = (RegionVarId.id, RegionGroupId.id) g_region_group
[@@deriving show]

type region_var_groups = region_var_group list [@@deriving show]

type __types_4 = unit (* to start the recursive group *)
(* __REPLACE4__ *)
[@@deriving show]
