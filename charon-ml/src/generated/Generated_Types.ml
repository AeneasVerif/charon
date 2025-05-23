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
module TraitTypeConstraintId = IdGen ()
module UnsolvedTraitId = IdGen ()
module RegionId = IdGen ()
module Disambiguator = IdGen ()
module FunDeclId = IdGen ()
module BodyId = IdGen ()

type ('id, 'x) vector = 'x list [@@deriving show, ord, eq]
type integer_type = Values.integer_type [@@deriving show, ord, eq]
type float_type = Values.float_type [@@deriving show, ord, eq]
type literal_type = Values.literal_type [@@deriving show, ord, eq]

(* Manually implemented because no type uses it (we use plain lists instead of
   vectors in generic_params), which causes visitor inference problems if we
   declare it within a visitor group. *)
type trait_type_constraint_id = TraitTypeConstraintId.id
[@@deriving show, ord, eq]

(** We define these types to control the name of the visitor functions *)
type ('id, 'name) indexed_var = {
  index : 'id;  (** Unique index identifying the variable *)
  name : 'name;  (** Variable name *)
}
[@@deriving show, ord, eq]

type fun_decl_id = (FunDeclId.id[@visitors.opaque])
and type_decl_id = (TypeDeclId.id[@visitors.opaque])
and global_decl_id = (GlobalDeclId.id[@visitors.opaque])
and trait_decl_id = (TraitDeclId.id[@visitors.opaque])
and trait_impl_id = (TraitImplId.id[@visitors.opaque])

(** The id of a translated item. *)
and any_decl_id =
  | IdType of type_decl_id
  | IdFun of fun_decl_id
  | IdGlobal of global_decl_id
  | IdTraitDecl of trait_decl_id
  | IdTraitImpl of trait_impl_id

(** The index of a binder, counting from the innermost. See [[DeBruijnVar]] for details. *)
and de_bruijn_id = int

(** Type-level variable.

    Variables are bound in groups. Each item has a top-level binding group in its [generic_params]
    field, and then inner binders are possible using the [RegionBinder<T>] and [Binder<T>] types.
    Each variable is linked to exactly one binder. The [Id] then identifies the specific variable
    among all those bound in that group.

    For instance, we have the following:
    {@rust[
    fn f<'a, 'b>(x: for<'c> fn(&'b u8, &'c u16, for<'d> fn(&'b u32, &'c u64, &'d u128)) -> u64) {}
         ^^^^^^         ^^       ^       ^          ^^       ^        ^        ^
           |       inner binder  |       |     inner binder  |        |        |
     top-level binder            |       |                   |        |        |
                           Bound(1, b)   |              Bound(2, b)   |     Bound(0, d)
                                         |                            |
                                     Bound(0, c)                 Bound(1, c)
    ]}

    To make consumption easier for projects that don't do heavy substitution, a micro-pass at the
    end changes the variables bound at the top-level (i.e. in the [GenericParams] of items) to be
    [Free]. This is an optional pass, we may add a flag to deactivate it. The example above
    becomes:
    {@rust[
    fn f<'a, 'b>(x: for<'c> fn(&'b u8, &'c u16, for<'d> fn(&'b u32, &'c u64, &'d u128)) -> u64) {}
         ^^^^^^         ^^       ^       ^          ^^       ^        ^        ^
           |       inner binder  |       |     inner binder  |        |        |
     top-level binder            |       |                   |        |        |
                              Free(b)    |                Free(b)     |     Bound(0, d)
                                         |                            |
                                     Bound(0, c)                 Bound(1, c)
    ]}

    At the moment only region variables can be bound in a non-top-level binder.
 *)
and 'a0 de_bruijn_var =
  | Bound of de_bruijn_id * 'a0
      (** A variable attached to the nth binder, counting from the innermost. *)
  | Free of 'a0
      (** A variable attached to the outermost binder (the one on the item). As explained above, This
          is not used in charon internals, only as a micro-pass before exporting the crate data.
       *)

and region_id = (RegionId.id[@visitors.opaque])
and type_var_id = (TypeVarId.id[@visitors.opaque])
and const_generic_var_id = (ConstGenericVarId.id[@visitors.opaque])
and trait_clause_id = (TraitClauseId.id[@visitors.opaque])

(** Const Generic Values. Either a primitive value, or a variable corresponding to a primitve value *)
and const_generic =
  | CgGlobal of global_decl_id  (** A global constant *)
  | CgVar of const_generic_var_id de_bruijn_var  (** A const generic variable *)
  | CgValue of literal  (** A concrete value *)
[@@deriving
  show,
    eq,
    ord,
    visitors
      {
        name = "iter_const_generic";
        monomorphic = [ "env" ];
        variety = "iter";
        ancestors = [ "iter_literal" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_const_generic";
        monomorphic = [ "env" ];
        variety = "map";
        ancestors = [ "map_literal" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "reduce_const_generic";
        monomorphic = [ "env" ];
        variety = "reduce";
        ancestors = [ "reduce_literal" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "mapreduce_const_generic";
        monomorphic = [ "env" ];
        variety = "mapreduce";
        ancestors = [ "mapreduce_literal" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

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
  end

(** Reference to a function declaration. *)
type fun_decl_ref = {
  fun_id : fun_decl_id;
  fun_generics : generic_args;  (** Generic arguments passed to the function. *)
}

(** Reference to a global declaration. *)
and global_decl_ref = {
  global_id : global_decl_id;
  global_generics : generic_args;
}

and trait_item_name = string

(** A region variable in a signature or binder. *)
and region_var = (region_id, string option) indexed_var

and region =
  | RVar of region_id de_bruijn_var
      (** Region variable. See [DeBruijnVar] for details. *)
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
  | Clause of trait_clause_id de_bruijn_var
      (** One of the local clauses.

          Example:
          {@rust[
          fn f<T>(...) where T : Foo
                             ^^^^^^^
                             Clause(0)
          ]}
       *)
  | ParentClause of trait_instance_id * trait_decl_id * trait_clause_id
      (** A parent clause

          Remark: the [TraitDeclId] gives the trait declaration which is
          implemented by the instance id from which we take the parent clause
          (see example below). It is not necessary and included for convenience.

          Remark: Ideally we should store a full [TraitRef] instead, but hax does not give us enough
          information to get the right generic args.

          Example:
          {@rust[
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
          ]}
       *)
  | Self
      (** The implicit [Self: Trait] clause. Present inside trait declarations, including trait
          method declarations. Not present in trait implementations as we can use [TraitImpl] intead.
       *)
  | BuiltinOrAuto of
      trait_decl_ref region_binder
      * trait_ref list
      * (trait_item_name * ty) list
      (** A trait implementation that is computed by the compiler, such as for built-in traits
          [Sized] or [FnMut]. This morally points to an invisible [impl] block; as such it contains
          the information we may need from one.

          Fields:
          - [trait_decl_ref]
          - [parent_trait_refs]:  The [ImplExpr]s required to satisfy the implied predicates on the trait declaration.
          E.g. since [FnMut: FnOnce], a built-in [T: FnMut] impl would have an [ImplExpr] for [T:
          FnOnce].
          - [types]:  The values of the associated types for this trait.
       *)
  | Dyn of trait_decl_ref region_binder
      (** The automatically-generated implementation for [dyn Trait]. *)
  | UnknownTrait of string  (** For error reporting. *)

(** A reference to a trait *)
and trait_ref = {
  trait_id : trait_instance_id;
  trait_decl_ref : trait_decl_ref region_binder;
      (** Not necessary, but useful *)
}

(** A predicate of the form [Type: Trait<Args>].

    About the generics, if we write:
    {@rust[
    impl Foo<bool> for String { ... }
    ]}

    The substitution is: [[String, bool]].
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

(** Each [GenericArgs] is meant for a corresponding [GenericParams]; this describes which one. *)
and generics_source =
  | GSItem of any_decl_id  (** A top-level item. *)
  | GSMethod of trait_decl_id * trait_item_name  (** A trait method. *)
  | GSBuiltin  (** A builtin item like [Box]. *)

(** A set of generic arguments. *)
and generic_args = {
  regions : region list;
  types : ty list;
  const_generics : const_generic list;
  trait_refs : trait_ref list;
}

(** A value of type [T] bound by regions. We should use [binder] instead but this causes name clash
    issues in the derived ocaml visitors.
    TODO: merge with [binder]
 *)
and 'a0 region_binder = {
  binder_regions : region_var list;
  binder_value : 'a0;
      (** Named this way to highlight accesses to the inner value that might be handling parameters
        incorrectly. Prefer using helper methods.
     *)
}

(** A predicate of the form [exists<T> where T: Trait].

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
          - tuples (including [unit], which is a 0-tuple)
          - built-in types (includes some primitive types, e.g., arrays or slices)
          The information on the nature of the ADT is stored in ([TypeId])[TypeId].
          The last list is used encode const generics, e.g., the size of an array

          Note: this is incorrectly named: this can refer to any valid [TypeDecl] including extern
          types.
       *)
  | TClosure of
      fun_decl_id * generic_args * ty list * (ty list * ty) region_binder
      (** A closure type, which is essentially a struct with builtin impls. Currently we don't
          translate the struct itself, only the function item that contains the closure's code.

          Fields:
          - [fun_id]:  The FunDecl item containing the code of the closure. That function takes the closure
          state as its first argument.
          - [parent_args]:  Generics that apply to the parent of this closure.
          Warning: hax may not handle nexted closure correctly yet.
          - [upvar_tys]:  The types of the variables captured by this closure.
          - [signature]:  The signature of the function that this closure represents.
       *)
  | TVar of type_var_id de_bruijn_var
  | TLiteral of literal_type
  | TNever
      (** The never type, for computations which don't return. It is sometimes
          necessary for intermediate variables. For instance, if we do (coming
          from the rust documentation):
          {@rust[
          let num: u32 = match get_a_number() {
              Some(num) => num,
              None => break,
          };
          ]}
          the second branch will have type [Never]. Also note that [Never]
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
          {@rust[
          trait Foo {
            type Bar; // type associated to the trait Foo
          }
          ]}
       *)
  | TDynTrait of existential_predicate
      (** [dyn Trait]

          This carries an existentially quantified list of predicates, e.g. [exists<T> where T:
          Into<u64>]. The predicate must quantify over a single type and no any regions or constants.

          TODO: we don't translate this properly yet.
       *)
  | TArrow of (ty list * ty) region_binder
      (** Arrow type, used for function pointers and reused for the unique type associated with each
          function item.
          This is a function signature with limited generics: it only supports lifetime generics, not
          other kinds of
          generics.
       *)
  | TError of string  (** A type that could not be computed or was incorrect. *)

(** Builtin types identifiers.

    WARNING: for now, all the built-in types are covariant in the generic
    parameters (if there are). Adding types which don't satisfy this
    will require to update the code abstracting the signatures (to properly
    take into account the lifetime constraints).

    TODO: update to not hardcode the types (except [Box] maybe) and be more
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
    eq,
    ord,
    visitors
      {
        name = "iter_ty";
        monomorphic = [ "env" ];
        variety = "iter";
        ancestors = [ "iter_ty_base_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_ty";
        monomorphic = [ "env" ];
        variety = "map";
        ancestors = [ "map_ty_base_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

(* Ancestors for the type_decl visitors *)
class ['self] iter_type_decl_base =
  object (self : 'self)
    inherit [_] iter_ty
    method visit_span : 'env -> span -> unit = fun _ _ -> ()
    method visit_attr_info : 'env -> attr_info -> unit = fun _ _ -> ()
  end

class ['self] map_type_decl_base =
  object (self : 'self)
    inherit [_] map_ty
    method visit_span : 'env -> span -> span = fun _ x -> x
    method visit_attr_info : 'env -> attr_info -> attr_info = fun _ x -> x
  end

(** (U)LLBC is a language with side-effects: a statement may abort in a way that isn't tracked by
    control-flow. The two kinds of abort are:
    - Panic (may unwind or not depending on compilation setting);
    - Undefined behavior:
 *)
type abort_kind =
  | Panic of name option  (** A built-in panicking function. *)
  | UndefinedBehavior  (** Undefined behavior in the rust abstract machine. *)

(** Meta information about an item (function, trait decl, trait impl, type decl, global). *)
and item_meta = {
  name : name;
  span : span;
  source_text : string option;
      (** The source code that corresponds to this item. *)
  attr_info : attr_info;  (** Attributes and visibility. *)
  is_local : bool;
      (** [true] if the type decl is a local type decl, [false] if it comes from an external crate. *)
  lang_item : string option;
      (** If the item is built-in, record its internal builtin identifier. *)
}

and disambiguator = (Disambiguator.id[@visitors.opaque])

(** See the comments for [Name] *)
and path_elem =
  | PeIdent of string * disambiguator
  | PeImpl of impl_elem * disambiguator

(** There are two kinds of [impl] blocks:
    - impl blocks linked to a type ("inherent" impl blocks following Rust terminology):
      {@rust[
      impl<T> List<T> { ...}
      ]}
    - trait impl blocks:
      {@rust[
      impl<T> PartialEq for List<T> { ...}
      ]}
    We distinguish the two.
 *)
and impl_elem = ImplElemTy of ty binder | ImplElemTrait of trait_impl_id

(** An item name/path

    A name really is a list of strings. However, we sometimes need to
    introduce unique indices to disambiguate. This mostly happens because
    of "impl" blocks:
      {@rust[
      impl<T> List<T> {
        ...
      }
      ]}

    A type in Rust can have several "impl" blocks, and  those blocks can
    contain items with similar names. For this reason, we need to disambiguate
    them with unique indices. Rustc calls those "disambiguators". In rustc, this
    gives names like this:
    - [betree_main::betree::NodeIdCounter{impl#0}::new]
    - note that impl blocks can be nested, and macros sometimes generate
      weird names (which require disambiguation):
      [betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}]

    Finally, the paths used by rustc are a lot more precise and explicit than
    those we expose in LLBC: for instance, every identifier belongs to a specific
    namespace (value namespace, type namespace, etc.), and is coupled with a
    disambiguator.

    On our side, we want to stay high-level and simple: we use string identifiers
    as much as possible, insert disambiguators only when necessary (whenever
    we find an "impl" block, typically) and check that the disambiguator is useless
    in the other situations (i.e., the disambiguator is always equal to 0).

    Moreover, the items are uniquely disambiguated by their (integer) ids
    ([TypeDeclId], etc.), and when extracting the code we have to deal with
    name clashes anyway. Still, we might want to be more precise in the future.

    Also note that the first path element in the name is always the crate name.
 *)
and name = (path_elem list[@visitors.opaque])

(** A type variable in a signature or binder. *)
and type_var = (type_var_id, string) indexed_var

(** A const generic variable in a signature or binder. *)
and const_generic_var = {
  index : const_generic_var_id;
      (** Index identifying the variable among other variables bound at the same level. *)
  name : string;  (** Const generic name *)
  ty : literal_type;  (** Type of the const generic *)
}

(** A trait predicate in a signature, of the form [Type: Trait<Args>]. This functions like a
    variable binder, to which variables of the form [TraitRefKind::Clause] can refer to.
 *)
and trait_clause = {
  clause_id : trait_clause_id;
      (** Index identifying the clause among other clauses bound at the same level. *)
  span : span option;
  trait : trait_decl_ref region_binder;  (** The trait that is implemented. *)
}

(** .0 outlives .1 *)
and ('a0, 'a1) outlives_pred = 'a0 * 'a1

(** A constraint over a trait associated type.

    Example:
    {@rust[
    T : Foo<S = String>
            ^^^^^^^^^^
    ]}
 *)
and trait_type_constraint = {
  trait_ref : trait_ref;
  type_name : trait_item_name;
  ty : ty;
}

and binder_kind =
  | BKTraitMethod of trait_decl_id * trait_item_name
      (** The parameters of a trait method. Used in the [methods] lists in trait decls and trait
          impls.
       *)
  | BKInherentImplBlock
      (** The parameters bound in a non-trait [impl] block. Used in the [Name]s of inherent methods. *)
  | BKOther  (** Some other use of a binder outside the main Charon ast. *)

(** A value of type [T] bound by generic parameters. Used in any context where we're adding generic
    parameters that aren't on the top-level item, e.g. [for<'a>] clauses (uses [RegionBinder] for
    now), trait methods, GATs (TODO).
 *)
and 'a0 binder = {
  binder_params : generic_params;
  binder_value : 'a0;
      (** Named this way to highlight accesses to the inner value that might be handling parameters
        incorrectly. Prefer using helper methods.
     *)
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
and type_decl = {
  def_id : type_decl_id;
  item_meta : item_meta;  (** Meta information associated with the item. *)
  generics : generic_params;
  kind : type_decl_kind;  (** The type kind: enum, struct, or opaque. *)
}

and variant_id = (VariantId.id[@visitors.opaque])
and field_id = (FieldId.id[@visitors.opaque])

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
  | TDeclError of string
      (** Used if an error happened during the extraction, and we don't panic
          on error.
       *)

and variant = {
  span : span;
  attr_info : attr_info;
  variant_name : string;
  fields : field list;
  discriminant : scalar_value;
      (** The discriminant value outputted by [std::mem::discriminant] for this variant. This is
        different than the discriminant stored in memory (the one controlled by [repr]).
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
    eq,
    ord,
    visitors
      {
        name = "iter_type_decl";
        monomorphic = [ "env" ];
        variety = "iter";
        ancestors = [ "iter_type_decl_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_type_decl";
        monomorphic = [ "env" ];
        variety = "map";
        ancestors = [ "map_type_decl_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]
