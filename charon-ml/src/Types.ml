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

(** Region variable ids. Used in function signatures. *)
module RegionVarId =
IdGen ()

(** Region ids. Used for symbolic executions. *)
module RegionId = IdGen ()

module RegionGroupId = IdGen ()

type ('id, 'name) indexed_var = {
  index : 'id;  (** Unique index identifying the variable *)
  name : 'name;  (** Variable name *)
}
[@@deriving show]

type type_var = (TypeVarId.id, string) indexed_var [@@deriving show]
type region_var = (RegionVarId.id, string option) indexed_var [@@deriving show]

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

type assumed_ty = Box | Vec | Option | Array | Slice | Str
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
class virtual ['self] map_const_generic_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_global_decl_id : 'env -> global_decl_id -> global_decl_id =
      fun _ x -> x

    method visit_const_generic_var_id
        : 'env -> const_generic_var_id -> const_generic_var_id =
      fun _ x -> x

    method visit_literal : 'env -> literal -> literal = fun _ x -> x
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
        concrete = false;
        polymorphic = false;
      }]

(** Ancestor for iter visitor for {!type: Types.ty} *)
class ['self] iter_ty_base =
  object (_self : 'self)
    inherit [_] iter_const_generic
    method visit_'r : 'env -> 'r -> unit = fun _ _ -> ()
    method visit_type_var_id : 'env -> type_var_id -> unit = fun _ _ -> ()
    method visit_type_id : 'env -> type_id -> unit = fun _ _ -> ()
    method visit_ref_kind : 'env -> ref_kind -> unit = fun _ _ -> ()
    method visit_literal_type : 'env -> literal_type -> unit = fun _ _ -> ()
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
  end

type 'r ty =
  | Adt of type_id * 'r list * 'r ty list * const_generic list
      (** {!Types.ty.Adt} encodes ADTs, tuples and assumed types *)
  | TypeVar of type_var_id
  | Literal of literal_type
  | Never
  | Ref of 'r * 'r ty * ref_kind
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
(* TODO: group Bool, Char, etc. in Primitive *)

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

type field = { meta : meta; field_name : string option; field_ty : sty }
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
  region_params : region_var list;
  type_params : type_var list;
  const_generic_params : const_generic_var list;
  kind : type_decl_kind;
  regions_hierarchy : region_var_groups;
      (** Stores the hierarchy between the regions (which regions have the
          same lifetime, which lifetime should end before which other lifetime,
          etc.) *)
}
[@@deriving show]
