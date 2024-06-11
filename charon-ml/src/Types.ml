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

(* TODO: Str should be a literal *)
type assumed_ty = TBox | TArray | TSlice | TStr

(** Type identifier for ADTs.

    ADTs are very general in our encoding: they account for "regular" ADTs,
    tuples and also assumed types.
*)
and type_id = TAdtId of type_decl_id | TTuple | TAssumed of assumed_ty

and ty =
  | TAdt of type_id * generic_args
      (** {!Types.ty.TAdt} encodes ADTs, tuples and assumed types *)
  | TVar of type_var_id
  | TLiteral of literal_type
  | TNever
  | TRef of region * ty * ref_kind
  | TRawPtr of ty * ref_kind
  | TTraitType of trait_ref * string
      (** The string is for the name of the associated type *)
  | TArrow of region_var list * ty list * ty

and trait_ref = {
  trait_id : trait_instance_id;
  generics : generic_args;
  trait_decl_ref : trait_decl_ref;
}

and trait_decl_ref = {
  trait_decl_id : trait_decl_id;
  decl_generics : generic_args; (* The name: annoying field collisions... *)
}

and generic_args = {
  regions : region list;
  types : ty list;
  const_generics : const_generic list;
  trait_refs : trait_ref list;
}

(** Identifier of a trait instance. *)
and trait_instance_id =
  | Self
      (** Reference to *self*, in case of trait declarations/implementations *)
  | TraitImpl of trait_impl_id  (** A specific implementation *)
  | BuiltinOrAuto of trait_decl_id
  | Clause of trait_clause_id
  | ParentClause of trait_instance_id * trait_decl_id * trait_clause_id
  | ItemClause of
      trait_instance_id * trait_decl_id * trait_item_name * trait_clause_id
  | TraitRef of trait_ref
      (** Not present in the Rust version of Charon.

          We need this case for instantiations: when calling a function which has
          trait clauses, for instance, we substitute the clauses refernced in the
          [Clause] and [Self] case with trait references.

          Remark: something potentially confusing is that [trait_clause_id] is used for
          different purposes. In the [Clause] case, a trait clause id identifies a local
          trait clause (which can thus be substituted). In the other cases, it references
          a sub-clause relative to a trait instance id.
       *)
  | FnPointer of ty
  | Closure of fun_decl_id * generic_args
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

(** Ancestor for iter visitor for {!type: Types.predicates} *)
class ['self] iter_predicates_base =
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

(** Ancestor for map visitor for {!type: Types.ty} *)
class virtual ['self] map_predicates_base =
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

and trait_clause = {
  clause_id : trait_clause_id;
  span : span option;
  trait_id : trait_decl_id;
  clause_generics : generic_args;
}

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
}

(** ('long, 'short) means that 'long outlives 'short *)
and region_outlives = region * region

(** (T, 'a) means that T outlives 'a *)
and type_outlives = ty * region

and trait_type_constraint = {
  trait_ref : trait_ref;
  type_name : trait_item_name;
  ty : ty;
}

and predicates = {
  regions_outlive : region_outlives list;
  types_outlive : type_outlives list;
  trait_type_constraints : trait_type_constraint list;
}
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_predicates";
        variety = "iter";
        ancestors = [ "iter_predicates_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
        polymorphic = false;
      },
    visitors
      {
        name = "map_predicates";
        variety = "map";
        ancestors = [ "map_predicates_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.map} *);
        concrete = false;
        polymorphic = false;
      }]

(** In implementation path elements we distinguish inherent impls (impl blocks
    for types) from trait impls *)
type impl_elem_kind = ImplElemTy of ty | ImplElemTrait of trait_decl_ref
[@@deriving show, ord]

(** An impl path element for [name] *)
type impl_elem = {
  disambiguator : Disambiguator.id;
  generics : generic_params;
  preds : predicates;
  kind : impl_elem_kind;
}
[@@deriving show, ord]

(** A path element for [name] *)
type path_elem = PeIdent of string * Disambiguator.id | PeImpl of impl_elem
[@@deriving show, ord]

(** A name *)
type name = path_elem list [@@deriving show, ord]

(** A group of regions.

    Results from a lifetime analysis: we group the regions with the same
    lifetime together, and compute the hierarchy between the regions.
    This is necessary to introduce the proper abstraction with the
    proper constraints, when evaluating a function call in symbolic mode.
*)
type ('rid, 'id) g_region_group = {
  id : 'id;
  regions : 'rid list;
  parents : 'id list;
}
[@@deriving show]

type region_var_group = (RegionVarId.id, RegionGroupId.id) g_region_group
[@@deriving show]

type region_var_groups = region_var_group list [@@deriving show]

type field = {
  item_meta : item_meta;
  field_name : string option;
  field_ty : ty;
}
[@@deriving show]

type variant = {
  span : span;
  variant_name : string;
  fields : field list;
      (** The fields can be indexed with {!FieldId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  discriminant : scalar_value;
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
  | Alias of ty
      (** A type alias. This only shows up as a top-level item; type aliases are inlined everywhere else. *)
  | Opaque
      (** An opaque type: either a local type marked as opaque, or an external type *)
[@@deriving show]

type type_decl = {
  def_id : TypeDeclId.id;
  item_meta : item_meta;
  is_local : bool;
  name : name;
  generics : generic_params;
  preds : predicates;
  kind : type_decl_kind;
}
[@@deriving show]
