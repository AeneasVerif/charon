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

type fun_decl_id = FunDeclId.id
and type_decl_id = TypeDeclId.id
and global_decl_id = GlobalDeclId.id
and trait_decl_id = TraitDeclId.id
and trait_impl_id = TraitImplId.id
and disambiguator = Disambiguator.id

(** The index of a binder, counting from the innermost. See [`DeBruijnVar`] for details. *)
and de_bruijn_id = int

(** Bound region variable.

    **Important**:
    ==============
    Similarly to what the Rust compiler does, we use De Bruijn indices to
    identify *groups* of bound variables, and variable identifiers to
    identity the variables inside the groups.

    For instance, we have the following:
    ```text
                        we compute the De Bruijn indices from here
                               VVVVVVVVVVVVVVVVVVVVVVV
    fn f<'a, 'b>(x: for<'c> fn(&'a u8, &'b u16, &'c u32) -> u64) {}
         ^^^^^^         ^^       ^       ^        ^
           |      De Bruijn: 0   |       |        |
     De Bruijn: 1                |       |        |
                           De Bruijn: 1  |    De Bruijn: 0
                              Var id: 0  |       Var id: 0
                                         |
                                   De Bruijn: 1
                                      Var id: 1
    ```
 *)
and ('a0, 'a1) de_bruijn_var =
  | Bound of de_bruijn_id * 'a0
      (** A variable attached to the nth binder, counting from the inside. *)
  | Free of 'a1
      (** A variable attached to an implicit binder outside all other binders. This is not present in
          translated code, and only provided as a convenience for convenient variable manipulation.
       *)

and type_var_id = TypeVarId.id
and const_generic_var_id = ConstGenericVarId.id
and trait_clause_id = TraitClauseId.id
and variant_id = VariantId.id
and field_id = FieldId.id [@@deriving show, ord]

let all_signed_int_types = [ Isize; I8; I16; I32; I64; I128 ]
let all_unsigned_int_types = [ Usize; U8; U16; U32; U64; U128 ]
let all_int_types = List.append all_signed_int_types all_unsigned_int_types

(** The variant id for [Option::None] *)
let option_none_id = VariantId.of_int 0

(** The variant id for [Option::Some] *)
let option_some_id = VariantId.of_int 1

(* Ancestors for the const_generic visitors *)
class ['self] iter_const_generic_base =
  object (self : 'self)
    inherit [_] iter_literal

    method visit_const_generic_var_id : 'env -> const_generic_var_id -> unit =
      fun _ _ -> ()

    method visit_fun_decl_id : 'env -> fun_decl_id -> unit = fun _ _ -> ()
    method visit_global_decl_id : 'env -> global_decl_id -> unit = fun _ _ -> ()
    method visit_de_bruijn_id : 'env -> de_bruijn_id -> unit = fun _ _ -> ()
    method visit_free_region_id : 'env -> free_region_id -> unit = fun _ _ -> ()

    method visit_bound_region_id : 'env -> bound_region_id -> unit =
      fun _ _ -> ()

    method visit_trait_clause_id : 'env -> trait_clause_id -> unit =
      fun _ _ -> ()

    method visit_trait_decl_id : 'env -> trait_decl_id -> unit = fun _ _ -> ()
    method visit_trait_impl_id : 'env -> trait_impl_id -> unit = fun _ _ -> ()
    method visit_type_decl_id : 'env -> type_decl_id -> unit = fun _ _ -> ()
    method visit_type_var_id : 'env -> type_var_id -> unit = fun _ _ -> ()
  end

class ['self] map_const_generic_base =
  object (self : 'self)
    inherit [_] map_literal

    method visit_const_generic_var_id
        : 'env -> const_generic_var_id -> const_generic_var_id =
      fun _ x -> x

    method visit_fun_decl_id : 'env -> fun_decl_id -> fun_decl_id = fun _ x -> x

    method visit_global_decl_id : 'env -> global_decl_id -> global_decl_id =
      fun _ x -> x

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> de_bruijn_id =
      fun _ x -> x

    method visit_free_region_id : 'env -> free_region_id -> free_region_id =
      fun _ x -> x

    method visit_bound_region_id : 'env -> bound_region_id -> bound_region_id =
      fun _ x -> x

    method visit_trait_clause_id : 'env -> trait_clause_id -> trait_clause_id =
      fun _ x -> x

    method visit_trait_decl_id : 'env -> trait_decl_id -> trait_decl_id =
      fun _ x -> x

    method visit_trait_impl_id : 'env -> trait_impl_id -> trait_impl_id =
      fun _ x -> x

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id =
      fun _ x -> x

    method visit_type_var_id : 'env -> type_var_id -> type_var_id = fun _ x -> x
  end

class virtual ['self] reduce_const_generic_base =
  object (self : 'self)
    inherit [_] reduce_literal

    method visit_const_generic_var_id : 'env -> const_generic_var_id -> 'a =
      fun _ _ -> self#zero

    method visit_fun_decl_id : 'env -> fun_decl_id -> 'a = fun _ _ -> self#zero

    method visit_global_decl_id : 'env -> global_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> 'a =
      fun _ _ -> self#zero

    method visit_free_region_id : 'env -> free_region_id -> 'a =
      fun _ _ -> self#zero

    method visit_bound_region_id : 'env -> bound_region_id -> 'a =
      fun _ _ -> self#zero

    method visit_trait_clause_id : 'env -> trait_clause_id -> 'a =
      fun _ _ -> self#zero

    method visit_trait_decl_id : 'env -> trait_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_trait_impl_id : 'env -> trait_impl_id -> 'a =
      fun _ _ -> self#zero

    method visit_type_decl_id : 'env -> type_decl_id -> 'a =
      fun _ _ -> self#zero

    method visit_type_var_id : 'env -> type_var_id -> 'a = fun _ _ -> self#zero
  end

class virtual ['self] mapreduce_const_generic_base =
  object (self : 'self)
    inherit [_] mapreduce_literal

    method visit_const_generic_var_id
        : 'env -> const_generic_var_id -> const_generic_var_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_fun_decl_id : 'env -> fun_decl_id -> fun_decl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_global_decl_id : 'env -> global_decl_id -> global_decl_id * 'a
        =
      fun _ x -> (x, self#zero)

    method visit_de_bruijn_id : 'env -> de_bruijn_id -> de_bruijn_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_free_region_id : 'env -> free_region_id -> free_region_id * 'a
        =
      fun _ x -> (x, self#zero)

    method visit_bound_region_id
        : 'env -> bound_region_id -> bound_region_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_clause_id
        : 'env -> trait_clause_id -> trait_clause_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_decl_id : 'env -> trait_decl_id -> trait_decl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_trait_impl_id : 'env -> trait_impl_id -> trait_impl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id * 'a =
      fun _ x -> (x, self#zero)

    method visit_type_var_id : 'env -> type_var_id -> type_var_id * 'a =
      fun _ x -> (x, self#zero)
  end

(** Const Generic Values. Either a primitive value, or a variable corresponding to a primitve value *)
type const_generic =
  | CgGlobal of global_decl_id  (** A global constant *)
  | CgVar of const_generic_var_id  (** A const generic variable *)
  | CgValue of literal  (** A concrete value *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_const_generic";
        variety = "iter";
        ancestors = [ "iter_const_generic_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_const_generic";
        variety = "map";
        ancestors = [ "map_const_generic_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "reduce_const_generic";
        variety = "reduce";
        ancestors = [ "reduce_const_generic_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "mapreduce_const_generic";
        variety = "mapreduce";
        ancestors = [ "mapreduce_const_generic_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

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

    method visit_de_bruijn_var
        : 'l 'r.
          ('env -> 'l -> unit) ->
          ('env -> 'r -> unit) ->
          'env ->
          ('l, 'r) de_bruijn_var ->
          unit =
      fun visit_bound visit_free env x ->
        match x with
        | Bound (dbid, varid) ->
            self#visit_de_bruijn_id env dbid;
            visit_bound env varid
        | Free varid -> visit_free env varid

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

    method visit_de_bruijn_var
        : 'l 'r.
          ('env -> 'l -> 'l) ->
          ('env -> 'r -> 'r) ->
          'env ->
          ('l, 'r) de_bruijn_var ->
          ('l, 'r) de_bruijn_var =
      fun visit_bound visit_free env x ->
        match x with
        | Bound (dbid, varid) ->
            let dbid = self#visit_de_bruijn_id env dbid in
            let varid = visit_bound env varid in
            Bound (dbid, varid)
        | Free varid ->
            let varid = visit_free env varid in
            Free varid

    method visit_region_var env (x : region_var) =
      self#visit_indexed_var self#visit_bound_region_id
        (self#visit_option self#visit_string)
        env x

    method visit_region_binder
        : 'a. ('env -> 'a -> 'a) -> 'env -> 'a region_binder -> 'a region_binder
        =
      fun visit_binder_value env x ->
        let { binder_regions; binder_value } = x in
        let binder_regions =
          self#visit_list self#visit_region_var env binder_regions
        in
        let binder_value = visit_binder_value env binder_value in
        { binder_regions; binder_value }
  end

(** Reference to a global declaration. *)
type global_decl_ref = {
  global_id : global_decl_id;
  global_generics : generic_args;
}

and trait_item_name = string

and region =
  | RVar of (bound_region_id, free_region_id) de_bruijn_var
      (** Region variable. See `DeBruijnVar` for details. *)
  | RStatic  (** Static region *)
  | RErased  (** Erased region *)

(** Identifier of a trait instance.
    This is derived from the trait resolution.

    Should be read as a path inside the trait clauses which apply to the current
    definition. Note that every path designated by [TraitInstanceId] refers
    to a *trait instance*, which is why the [Clause] variant may seem redundant
    with some of the other variants.
 *)
and trait_instance_id =
  | TraitImpl of trait_impl_id * generic_args
      (** A specific top-level implementation item. *)
  | Clause of trait_clause_id
      (** One of the local clauses.

          Example:
          ```text
          fn f<T>(...) where T : Foo
                             ^^^^^^^
                             Clause(0)
          ```
       *)
  | ParentClause of trait_instance_id * trait_decl_id * trait_clause_id
      (** A parent clause

          Remark: the [TraitDeclId] gives the trait declaration which is
          implemented by the instance id from which we take the parent clause
          (see example below). It is not necessary and included for convenience.

          Remark: Ideally we should store a full `TraitRef` instead, but hax does not give us enough
          information to get the right generic args.

          Example:
          ```text
          trait Foo1 {}
          trait Foo2 { fn f(); }

          trait Bar : Foo1 + Foo2 {}
                      ^^^^   ^^^^
                             parent clause 1
              parent clause 0

          fn g<T : Bar>(x : T) {
            x.f()
            ^^^^^
            Parent(Clause(0), Bar, 1)::f(x)
                                   ^
                                   parent clause 1 of clause 0
                              ^^^
                       clause 0 implements Bar
          }
          ```
       *)
  | Self
      (** Self, in case of trait declarations/implementations.

          Putting [Self] at the end on purpose, so that when ordering the clauses
          we start with the other clauses (in particular, the local clauses). It
          is useful to give priority to the local clauses when solving the trait
          obligations which are fullfilled by the trait parameters.
       *)
  | BuiltinOrAuto of trait_decl_ref region_binder
      (** A specific builtin trait implementation like [core::marker::Sized] or
          auto trait implementation like [core::marker::Syn].
       *)
  | Dyn of trait_decl_ref region_binder
      (** The automatically-generated implementation for `dyn Trait`. *)
  | UnknownTrait of string  (** For error reporting. *)

(** A reference to a trait *)
and trait_ref = {
  trait_id : trait_instance_id;
  trait_decl_ref : trait_decl_ref region_binder;
      (** Not necessary, but useful *)
}

(** A predicate of the form `Type: Trait<Args>`.

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

(** A reference to a tait impl, using the provided arguments. *)
and trait_impl_ref = {
  trait_impl_id : trait_impl_id;
  impl_generics : generic_args;
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

and ref_kind = RMut | RShared

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
  | TBuiltin of builtin_ty
      (** Built-in type. Either a primitive type like array or slice, or a
          non-primitive type coming from a standard library
          and that we handle like a primitive type. Types falling into this
          category include: Box, Vec, Cell...
          The Array and Slice types were initially modelled as primitive in
          the [Ty] type. We decided to move them to built-in types as it allows
          for more uniform treatment throughout the codebase.
       *)

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
  | TArrow of (ty list * ty) region_binder
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
and builtin_ty =
  | TBox  (** Boxes are de facto a primitive type. *)
  | TArray  (** Primitive type *)
  | TSlice  (** Primitive type *)
  | TStr  (** Primitive type *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_ty";
        variety = "iter";
        ancestors = [ "iter_ty_base_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_ty";
        variety = "map";
        ancestors = [ "map_ty_base_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

(* Ancestors for the generic_params visitors *)
class ['self] iter_generic_params_base =
  object (self : 'self)
    inherit [_] iter_ty
    method visit_span : 'env -> span -> unit = fun _ _ -> ()
  end

class ['self] map_generic_params_base =
  object (self : 'self)
    inherit [_] map_ty
    method visit_span : 'env -> span -> span = fun _ x -> x
  end

(** A type variable in a signature or binder. *)
type type_var = (type_var_id, string) indexed_var

(** A const generic variable in a signature or binder. *)
and const_generic_var = {
  index : const_generic_var_id;
      (** Index identifying the variable among other variables bound at the same level. *)
  name : string;  (** Const generic name *)
  ty : literal_type;  (** Type of the const generic *)
}

(** A trait predicate in a signature, of the form `Type: Trait<Args>`. This functions like a
    variable binder, to which variables of the form `TraitRefKind::Clause` can refer to.
 *)
and trait_clause = {
  clause_id : trait_clause_id;
      (** Index identifying the clause among other clauses bound at the same level. *)
  span : span option;
  trait : trait_decl_ref region_binder;  (** The trait that is implemented. *)
}

and region_outlives = (region, region) outlives_pred
and type_outlives = (ty, region) outlives_pred

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

(** Generic parameters for a declaration.
    We group the generics which come from the Rust compiler substitutions
    (the regions, types and const generics) as well as the trait clauses.
    The reason is that we consider that those are parameters that need to
    be filled. We group in a different place the predicates which are not
    trait clauses, because those enforce constraints but do not need to
    be filled with witnesses/instances.
 *)
and generic_params = {
  regions : region_var list;
  types : type_var list;
  const_generics : const_generic_var list;
  trait_clauses : trait_clause list;
  regions_outlive : (region, region) outlives_pred region_binder list;
      (** The first region in the pair outlives the second region *)
  types_outlive : (ty, region) outlives_pred region_binder list;
      (** The type outlives the region *)
  trait_type_constraints : trait_type_constraint region_binder list;
      (** Constraints over trait associated types *)
}
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_generic_params";
        variety = "iter";
        ancestors = [ "iter_generic_params_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_generic_params";
        variety = "map";
        ancestors = [ "map_generic_params_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
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

(* Ancestors for the type_decl visitors *)
class ['self] iter_type_decl_base =
  object (self : 'self)
    inherit [_] iter_generic_params
    method visit_attr_info : 'env -> attr_info -> unit = fun _ _ -> ()
    method visit_item_meta : 'env -> item_meta -> unit = fun _ _ -> ()
  end

class ['self] map_type_decl_base =
  object (self : 'self)
    inherit [_] map_generic_params
    method visit_attr_info : 'env -> attr_info -> attr_info = fun _ x -> x
    method visit_item_meta : 'env -> item_meta -> item_meta = fun _ x -> x
  end

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
  | TError of string
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
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_type_decl";
        variety = "iter";
        ancestors = [ "iter_type_decl_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_type_decl";
        variety = "map";
        ancestors = [ "map_type_decl_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

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

type region_db_var = (bound_region_id, free_region_id) de_bruijn_var
[@@deriving show]

type region_var_group = (BoundRegionId.id, RegionGroupId.id) g_region_group
[@@deriving show]

type region_var_groups = region_var_group list [@@deriving show]

(** Type with erased regions (this only has an informative purpose) *)
type ety = ty

(** Type with non-erased regions (this only has an informative purpose) *)
and rty = ty [@@deriving show, ord]
