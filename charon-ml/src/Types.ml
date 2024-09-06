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
type float_type = Values.float_type [@@deriving show, ord]

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

(** Reference to a global declaration. *)
type global_decl_ref = {
  global_id : global_decl_id;
  global_generics : generic_args;
}

(** A reference to a trait *)
and trait_ref = {
  trait_id : trait_instance_id;
  trait_decl_ref : trait_decl_ref;  (** Not necessary, but useful *)
}

(** Reference to a trait declaration.

    About the generics, if we write:
    ```text
    impl Foo<bool> for String { ... }
    ```

    The substitution is: `[String, bool]`.
 *)
and trait_decl_ref = {
  trait_decl_id : trait_decl_id;
  decl_generics : generic_args;
}

and generic_args = {
  regions : region list;
  types : ty list;
  const_generics : const_generic list;
  trait_refs : trait_ref list;
}

(** A predicate of the form `exists<T> where T: Trait`.

    TODO: store something useful here
 *)
and existential_predicate = unit

(** Type identifier.

    Allows us to factorize the code for built-in types, adts and tuples
 *)
and type_id =
  | TAdtId of type_decl_id
      (** A "regular" ADT type.

          Includes transparent ADTs and opaque ADTs (local ADTs marked as opaque,
          and external ADTs).
       *)
  | TTuple
  | TAssumed of assumed_ty
      (** Built-in type. Either a primitive type like array or slice, or a
          non-primitive type coming from a standard library
          and that we handle like a primitive type. Types falling into this
          category include: Box, Vec, Cell...
          The Array and Slice types were initially modelled as primitive in
          the [Ty] type. We decided to move them to built-in types as it allows
          for more uniform treatment throughout the codebase.
       *)

(** A type. *)
and ty =
  | TAdt of type_id * generic_args
      (** An ADT.
          Note that here ADTs are very general. They can be:
          - user-defined ADTs
          - tuples (including `unit`, which is a 0-tuple)
          - built-in types (includes some primitive types, e.g., arrays or slices)
          The information on the nature of the ADT is stored in (`TypeId`)[TypeId].
          The last list is used encode const generics, e.g., the size of an array

          Note: this is incorrectly named: this can refer to any valid `TypeDecl` including extern
          types.
       *)
  | TVar of type_var_id
  | TLiteral of literal_type
  | TNever
      (** The never type, for computations which don't return. It is sometimes
          necessary for intermediate variables. For instance, if we do (coming
          from the rust documentation):
          ```text
          let num: u32 = match get_a_number() {
              Some(num) => num,
              None => break,
          };
          ```
          the second branch will have type `Never`. Also note that `Never`
          can be coerced to any type.

          Note that we eliminate the variables which have this type in a micro-pass.
          As statements don't have types, this type disappears eventually disappears
          from the AST.
       *)
  | TRef of region * ty * ref_kind  (** A borrow *)
  | TRawPtr of ty * ref_kind  (** A raw pointer. *)
  | TTraitType of trait_ref * trait_item_name
      (** A trait associated type

          Ex.:
          ```text
          trait Foo {
            type Bar; // type associated to the trait Foo
          }
          ```
       *)
  | TDynTrait of existential_predicate
      (** `dyn Trait`

          This carries an existentially quantified list of predicates, e.g. `exists<T> where T:
          Into<u64>`. The predicate must quantify over a single type and no any regions or constants.

          TODO: we don't translate this properly yet.
       *)
  | TArrow of region_var list * ty list * ty
      (** Arrow type, used in particular for the local function pointers.
          This is essentially a "constrained" function signature:
          arrow types can only contain generic lifetime parameters
          (no generic types), no predicates, etc.
       *)

(** Builtin types identifiers.

    WARNING: for now, all the built-in types are covariant in the generic
    parameters (if there are). Adding types which don't satisfy this
    will require to update the code abstracting the signatures (to properly
    take into account the lifetime constraints).

    TODO: update to not hardcode the types (except `Box` maybe) and be more
    modular.
    TODO: move to builtins.rs?
 *)
and assumed_ty =
  | TBox  (** Boxes are de facto a primitive type. *)
  | TArray  (** Primitive type *)
  | TSlice  (** Primitive type *)
  | TStr  (** Primitive type *)

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
(* Hand-written because we add an extra variant not present on the rust side *)

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

(** A predicate of the form `Type: Trait<Args>`. *)
and trait_clause = {
  clause_id : trait_clause_id;
      (** We use this id when solving trait constraints, to be able to refer
        to specific where clauses when the selected trait actually is linked
        to a parameter.
     *)
  span : span option;
  trait : trait_decl_ref;  (** The trait that is implemented. *)
}

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

(** A constraint over a trait associated type.

    Example:
    ```text
    T : Foo<S = String>
            ^^^^^^^^^^
    ```
 *)
and trait_type_constraint = {
  trait_ref : trait_ref;
  type_name : trait_item_name;
  ty : ty;
}
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

(** Meta information about an item (function, trait decl, trait impl, type decl, global). *)
type item_meta = {
  name : name;
  span : span;
  source_text : string option;
      (** The source code that corresponds to this item. *)
  attr_info : attr_info;  (** Attributes and visibility. *)
  is_local : bool;
      (** `true` if the type decl is a local type decl, `false` if it comes from an external crate. *)
}

(** See the comments for [Name] *)
and path_elem =
  | PeIdent of string * disambiguator
  | PeImpl of impl_elem * disambiguator

(** There are two kinds of `impl` blocks:
    - impl blocks linked to a type ("inherent" impl blocks following Rust terminology):
      ```text
      impl<T> List<T> { ...}
      ```
    - trait impl blocks:
      ```text
      impl<T> PartialEq for List<T> { ...}
      ```
    We distinguish the two.
 *)
and impl_elem =
  | ImplElemTy of generic_params * ty
  | ImplElemTrait of trait_impl_id

(** An item name/path

    A name really is a list of strings. However, we sometimes need to
    introduce unique indices to disambiguate. This mostly happens because
    of "impl" blocks:
      ```text
      impl<T> List<T> {
        ...
      }
      ```

    A type in Rust can have several "impl" blocks, and  those blocks can
    contain items with similar names. For this reason, we need to disambiguate
    them with unique indices. Rustc calls those "disambiguators". In rustc, this
    gives names like this:
    - `betree_main::betree::NodeIdCounter{impl#0}::new`
    - note that impl blocks can be nested, and macros sometimes generate
      weird names (which require disambiguation):
      `betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}`

    Finally, the paths used by rustc are a lot more precise and explicit than
    those we expose in LLBC: for instance, every identifier belongs to a specific
    namespace (value namespace, type namespace, etc.), and is coupled with a
    disambiguator.

    On our side, we want to stay high-level and simple: we use string identifiers
    as much as possible, insert disambiguators only when necessary (whenever
    we find an "impl" block, typically) and check that the disambiguator is useless
    in the other situations (i.e., the disambiguator is always equal to 0).

    Moreover, the items are uniquely disambiguated by their (integer) ids
    (`TypeDeclId`, etc.), and when extracting the code we have to deal with
    name clashes anyway. Still, we might want to be more precise in the future.

    Also note that the first path element in the name is always the crate name.
 *)
and name = path_elem list [@@deriving show, ord]

(* Hand-written because these don't exist on the rust side *)

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

(** A type declaration.

    Types can be opaque or transparent.

    Transparent types are local types not marked as opaque.
    Opaque types are the others: local types marked as opaque, and non-local
    types (coming from external dependencies).

    In case the type is transparent, the declaration also contains the
    type definition (see [TypeDeclKind]).

    A type can only be an ADT (structure or enumeration), as type aliases are
    inlined in MIR.
 *)
type type_decl = {
  def_id : type_decl_id;
  item_meta : item_meta;  (** Meta information associated with the item. *)
  generics : generic_params;
  kind : type_decl_kind;  (** The type kind: enum, struct, or opaque. *)
}

and type_decl_kind =
  | Struct of field list
  | Enum of variant list
  | Union of field list
  | Opaque
      (** An opaque type.

          Either a local type marked as opaque, or an external type.
       *)
  | Alias of ty
      (** An alias to another type. This only shows up in the top-level list of items, as rustc
          inlines uses of type aliases everywhere else.
       *)
  | Error of string
      (** Used if an error happened during the extraction, and we don't panic
          on error.
       *)

and variant = {
  span : span;
  attr_info : attr_info;
  variant_name : string;
  fields : field list;
  discriminant : scalar_value;
      (** The discriminant used at runtime. This is used in `remove_read_discriminant` to match up
        `SwitchInt` targets with the corresponding `Variant`.
     *)
}

and field = {
  span : span;
  attr_info : attr_info;
  field_name : string option;
  field_ty : ty;
}
[@@deriving show]
