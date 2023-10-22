open Identifiers
open Names
open Meta
open PrimitiveValues
module TypeVarId = IdGen ()
module TypeDeclId = IdGen ()
module VariantId = IdGen ()
module FieldId = IdGen ()
module GlobalDeclId = IdGen ()
module ConstGenericVarId = IdGen ()
module TraitDeclId = IdGen ()
module TraitImplId = IdGen ()
module TraitClauseId = IdGen ()

(** Region variable ids. Used in function signatures. *)
module RegionVarId =
IdGen ()

(** Region ids. Used for symbolic executions. *)
module RegionId = IdGen ()

module RegionGroupId = IdGen ()

(** We define this type to control the name of the visitor functions
    (see e.g., {!Types.iter_ty_base} and {!Types.TypeVar}).
  *)
type type_var_id = TypeVarId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type const_generic_var_id = ConstGenericVarId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type global_decl_id = GlobalDeclId.id [@@deriving show, ord]

type integer_type = PrimitiveValues.integer_type [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type variant_id = VariantId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type field_id = FieldId.id [@@deriving show, ord]

(** Same remark as for {!type_var_id} *)
type type_decl_id = TypeDeclId.id [@@deriving show, ord]

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

type ('id, 'name) indexed_var = {
  index : 'id;  (** Unique index identifying the variable *)
  name : 'name;  (** Variable name *)
}
[@@deriving show]

type type_var = (TypeVarId.id, string) indexed_var [@@deriving show]
type region_var = (RegionVarId.id, string option) indexed_var [@@deriving show]
type literal_type = PrimitiveValues.literal_type [@@deriving show, ord]

type const_generic_var = {
  index : ConstGenericVarId.id;
  name : string;
  ty : literal_type;
}
[@@deriving show, ord]

(** A region.

    Regions are used in function signatures (in which case we use region variable
    ids) and in symbolic variables and projections (in which case we use region
    ids).
 *)
type 'rid region =
  | Static  (** Static region *)
  | Var of 'rid  (** Non-static region *)
[@@deriving show, ord]

(** The type of erased regions.

    We could use unit, but having a dedicated type makes things more explicit.
 *)
type erased_region = Erased [@@deriving show, ord]

(** A group of regions.

    Results from a lifetime analysis: we group the regions with the same
    lifetime together, and compute the hierarchy between the regions.
    This is necessary to introduce the proper abstraction with the
    proper constraints, when evaluating a function call in symbolic mode.
*)
type ('id, 'r) g_region_group = {
  id : 'id;
  regions : 'r list;
  parents : 'id list;
}
[@@deriving show]

type ('r, 'id) g_region_groups = ('r, 'id) g_region_group list [@@deriving show]

type region_var_group = (RegionGroupId.id, RegionVarId.id) g_region_group
[@@deriving show]

type region_var_groups = (RegionGroupId.id, RegionVarId.id) g_region_groups
[@@deriving show]

let all_signed_int_types = [ Isize; I8; I16; I32; I64; I128 ]
let all_unsigned_int_types = [ Usize; U8; U16; U32; U64; U128 ]
let all_int_types = List.append all_signed_int_types all_unsigned_int_types

type ref_kind = Mut | Shared [@@deriving show, ord]

(* TODO: Str should be a literal *)
type assumed_ty = Box | Option | Array | Slice | Str | Range
[@@deriving show, ord]

(** The variant id for [Option::None] *)
let option_none_id = VariantId.of_int 0

(** The variant id for [Option::Some] *)
let option_some_id = VariantId.of_int 1

(** Type identifier for ADTs.

    ADTs are very general in our encoding: they account for "regular" ADTs,
    tuples and also assumed types.
*)
type type_id = AdtId of TypeDeclId.id | Tuple | Assumed of assumed_ty
[@@deriving show, ord]

(** Ancestor for iter visitor for {!Types.const_generic} *)
class ['self] iter_const_generic_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter
    method visit_global_decl_id : 'env -> global_decl_id -> unit = fun _ _ -> ()

    method visit_const_generic_var_id : 'env -> const_generic_var_id -> unit =
      fun _ _ -> ()

    method visit_literal : 'env -> literal -> unit = fun _ _ -> ()
  end

(** Ancestor for map visitor for {!Types.const_generic} *)
class ['self] map_const_generic_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_global_decl_id : 'env -> global_decl_id -> global_decl_id =
      fun _ x -> x

    method visit_const_generic_var_id
        : 'env -> const_generic_var_id -> const_generic_var_id =
      fun _ x -> x

    method visit_literal : 'env -> literal -> literal = fun _ x -> x
  end

(** Ancestor for reduce visitor for {!Types.const_generic} *)
class virtual ['self] reduce_const_generic_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce

    method visit_global_decl_id : 'env -> global_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_const_generic_var_id : 'env -> const_generic_var_id -> 'a =
      fun _ _ -> self#zero

    method visit_literal : 'env -> literal -> 'a = fun _ _ -> self#zero
  end

(** Ancestor for mapreduce visitor for {!Types.const_generic} *)
class virtual ['self] mapreduce_const_generic_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.mapreduce

    method visit_global_decl_id : 'env -> global_decl_id -> global_decl_id * 'a
        =
      fun _ x -> (x, self#zero)

    method visit_const_generic_var_id
        : 'env -> const_generic_var_id -> const_generic_var_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_literal : 'env -> literal -> literal * 'a =
      fun _ x -> (x, self#zero)
  end

(** Remark: we have to use long names because otherwise we have collisions in
    the functions derived for the visitors *)
type const_generic =
  | ConstGenericGlobal of global_decl_id
  | ConstGenericVar of const_generic_var_id
  | ConstGenericValue of literal
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
  object (_self : 'self)
    inherit [_] iter_const_generic
    method visit_'r : 'env -> 'r -> unit = fun _ _ -> ()
    method visit_type_var_id : 'env -> type_var_id -> unit = fun _ _ -> ()
    method visit_type_id : 'env -> type_id -> unit = fun _ _ -> ()
    method visit_ref_kind : 'env -> ref_kind -> unit = fun _ _ -> ()
    method visit_literal_type : 'env -> literal_type -> unit = fun _ _ -> ()

    method visit_trait_item_name : 'env -> trait_item_name -> unit =
      fun _ _ -> ()

    method visit_trait_decl_id : 'env -> trait_decl_id -> unit = fun _ _ -> ()
    method visit_trait_impl_id : 'env -> trait_impl_id -> unit = fun _ _ -> ()

    method visit_trait_clause_id : 'env -> trait_clause_id -> unit =
      fun _ _ -> ()
  end

(** Ancestor for map visitor for {!type: Types.ty} *)
class virtual ['self] map_ty_base =
  object (_self : 'self)
    inherit [_] map_const_generic
    method virtual visit_'r : 'env -> 'r -> 's

    method visit_type_var_id : 'env -> type_var_id -> type_var_id =
      fun _ id -> id

    method visit_type_id : 'env -> type_id -> type_id = fun _ id -> id
    method visit_ref_kind : 'env -> ref_kind -> ref_kind = fun _ rk -> rk

    method visit_literal_type : 'env -> literal_type -> literal_type =
      fun _ x -> x

    method visit_trait_item_name : 'env -> trait_item_name -> trait_item_name =
      fun _ x -> x

    method visit_trait_decl_id : 'env -> trait_decl_id -> trait_decl_id =
      fun _ x -> x

    method visit_trait_impl_id : 'env -> trait_impl_id -> trait_impl_id =
      fun _ x -> x

    method visit_trait_clause_id : 'env -> trait_clause_id -> trait_clause_id =
      fun _ x -> x
  end

(* TODO: we should prefix the type variants with "T", this would avoid collisions *)
type 'r ty =
  | Adt of type_id * 'r generic_args
      (** {!Types.ty.Adt} encodes ADTs, tuples and assumed types *)
  | TypeVar of type_var_id
  | Literal of literal_type
  | Never
  | Ref of 'r * 'r ty * ref_kind
  | TraitType of 'r trait_ref * 'r generic_args * string
      (** The string is for the name of the associated type *)
  | Arrow of 'r ty list * 'r ty

and 'r trait_ref = {
  trait_id : 'r trait_instance_id;
  generics : 'r generic_args;
  trait_decl_ref : 'r trait_decl_ref;
}

and 'r trait_decl_ref = {
  trait_decl_id : trait_decl_id;
  decl_generics : 'r generic_args; (* The name: annoying field collisions... *)
}

and 'r generic_args = {
  regions : 'r list;
  types : 'r ty list;
  const_generics : const_generic list;
  trait_refs : 'r trait_ref list;
}

(** Identifier of a trait instance. *)
and 'r trait_instance_id =
  | Self
      (** Reference to *self*, in case of trait declarations/implementations *)
  | TraitImpl of trait_impl_id  (** A specific implementation *)
  | BuiltinOrAuto of trait_decl_id
  | Clause of trait_clause_id
  | ParentClause of 'r trait_instance_id * trait_decl_id * trait_clause_id
  | ItemClause of
      'r trait_instance_id * trait_decl_id * trait_item_name * trait_clause_id
  | TraitRef of 'r trait_ref
      (** Not present in the Rust version of Charon.

          We need this case for instantiations: when calling a function which has
          trait clauses, for instance, we substitute the clauses refernced in the
          [Clause] and [Self] case with trait references.

          Remark: something potentially confusing is that [trait_clause_id] is used for
          different purposes. In the [Clause] case, a trait clause id identifies a local
          trait clause (which can thus be substituted). In the other cases, it references
          a sub-clause relative to a trait instance id.
       *)
  | FnPointer of 'r ty
  | UnknownTrait of string
      (** Not present in the Rust version of Charon.

        We use this in the substitutions, to substitute [Self] when [Self] shouldn't
        appear: this allows us to track errors by making sure [Self] indeed did not
        appear.
      *)
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

(** Generic type with regions *)
type 'r gr_ty = 'r region ty [@@deriving show, ord]

(** *S*ignature types.

    Used in function signatures and type definitions.
 *)
type sty = RegionVarId.id gr_ty [@@deriving show, ord]

(** Type with *R*egions.

    Used to project borrows/loans inside of abstractions, during symbolic
    execution.
 *)
type rty = RegionId.id gr_ty [@@deriving show, ord]

(** Type with *E*rased regions.

    Used in function bodies, "regular" value types, etc.
 *)
type ety = erased_region ty [@@deriving show, ord]

type sgeneric_args = RegionVarId.id region generic_args [@@deriving show, ord]
type egeneric_args = erased_region generic_args [@@deriving show, ord]
type rgeneric_args = RegionId.id region generic_args [@@deriving show, ord]
type strait_ref = RegionVarId.id region trait_ref [@@deriving show, ord]
type etrait_ref = erased_region trait_ref [@@deriving show, ord]
type rtrait_ref = RegionId.id region trait_ref [@@deriving show, ord]
type strait_decl_ref = RegionVarId.id region trait_decl_ref [@@deriving show]
type etrait_decl_ref = erased_region trait_decl_ref [@@deriving show]
type rtrait_decl_ref = RegionId.id region trait_decl_ref [@@deriving show]

type strait_instance_id = RegionVarId.id region trait_instance_id
[@@deriving show]

type etrait_instance_id = erased_region trait_instance_id [@@deriving show]
type rtrait_instance_id = RegionId.id region trait_instance_id [@@deriving show]

type field = { meta : meta; field_name : string option; field_ty : sty }
[@@deriving show]

type trait_clause = {
  clause_id : trait_clause_id;
  meta : meta;
  trait_id : trait_decl_id;
  generics : sgeneric_args;
}
[@@deriving show]

type generic_params = {
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
}
[@@deriving show]

type region_outlives = region_var_id region * region_var_id region
[@@deriving show]

type type_outlives = sty * region_var_id region [@@deriving show]

type 'r trait_type_constraint = {
  trait_ref : 'r trait_ref;
  generics : 'r generic_args;
  type_name : trait_item_name;
  ty : 'r ty;
}
[@@deriving show]

type strait_type_constraint = RegionVarId.id region trait_type_constraint
[@@deriving show]

type etrait_type_constraint = erased_region trait_type_constraint
[@@deriving show]

type rtrait_type_constraint = RegionId.id region trait_type_constraint
[@@deriving show]

type predicates = {
  regions_outlive : region_outlives list;
  types_outlive : type_outlives list;
  trait_type_constraints : strait_type_constraint list;
}
[@@deriving show]

type variant = {
  meta : meta;
  variant_name : string;
  fields : field list;
      (** The fields can be indexed with {!FieldId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
}
[@@deriving show]

type type_decl_kind =
  | Struct of field list
      (** The fields of the structure can be indexed with {!FieldId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  | Enum of variant list
      (** The variants of the enumeration can be indexed with {!VariantId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  | Opaque
      (** An opaque type: either a local type marked as opaque, or an external type *)
[@@deriving show]

type type_decl = {
  def_id : TypeDeclId.id;
  meta : meta;
  name : type_name;
  generics : generic_params;
  preds : predicates;
  kind : type_decl_kind;
  regions_hierarchy : region_var_groups;
      (** Stores the hierarchy between the regions (which regions have the
          same lifetime, which lifetime should end before which other lifetime,
          etc.) *)
}
[@@deriving show]
