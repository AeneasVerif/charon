(** WARNING: this file is partially auto-generated. Do not edit `Types.ml` by
    hand. Edit `Types.template.ml` instead, or improve the code generation tool
    so avoid the need for hand-writing things.

    `Types.template.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`. *)

open Identifiers
include Generated_Meta
open Generated_Values
module TypeVarId = IdGen ()
module VariantId = IdGen ()
module FieldId = IdGen ()
module ConstGenericVarId = IdGen ()
module TraitClauseId = IdGen ()
module TraitTypeConstraintId = IdGen ()
module UnsolvedTraitId = IdGen ()
module RegionId = IdGen ()
module Disambiguator = IdGen ()

type integer_type = Values.integer_type [@@deriving show, ord, eq]
type float_type = Values.float_type [@@deriving show, ord, eq]
type scalar_type = Values.scalar_type [@@deriving show, ord, eq]

(* A range that includes both endpoints. *)
type 'a range_inclusive = 'a * 'a [@@deriving show, ord, eq]

(* Manually implemented because no type uses it (we use plain lists instead of
   vectors in generic_params), which causes visitor inference problems if we
   declare it within a visitor group. *)
type trait_type_constraint_id = TraitTypeConstraintId.id
[@@deriving show, ord, eq]

type 'a fun_decl_id_map = 'a FunDeclId.Map.t
and 'a global_decl_id_map = 'a GlobalDeclId.Map.t
and 'a type_decl_id_map = 'a TypeDeclId.Map.t
and 'a trait_decl_id_map = 'a TraitDeclId.Map.t
and 'a trait_impl_id_map = 'a TraitImplId.Map.t
and 'a trait_method_id_map = 'a TraitMethodId.Map.t
and 'a assoc_type_id_map = 'a AssocTypeId.Map.t [@@deriving show, eq, ord]
and 'a assoc_const_id_map = 'a AssocConstId.Map.t [@@deriving show, eq, ord]

let hash_fun_decl_id_map = FunDeclId.Map.hash
let hash_global_decl_id_map = GlobalDeclId.Map.hash
let hash_type_decl_id_map = TypeDeclId.Map.hash
let hash_trait_decl_id_map = TraitDeclId.Map.hash
let hash_trait_impl_id_map = TraitImplId.Map.hash
let hash_trait_method_id_map = TraitMethodId.Map.hash
let hash_assoc_type_id_map = AssocTypeId.Map.hash
let hash_assoc_const_id_map = AssocConstId.Map.hash
let hash_range_inclusive hash_a (x, y) = HashBasic.combine (hash_a x) (hash_a y)

(** The index of a binder, counting from the innermost. See [[DeBruijnVar]] for
    details. *)
type de_bruijn_id = int

(** Type-level variable.

    Variables are bound in groups. Each item has a top-level binding group in
    its [generic_params] field, and then inner binders are possible using the
    [RegionBinder<T>] and [Binder<T>] types. Each variable is linked to exactly
    one binder. The [Id] then identifies the specific variable among all those
    bound in that group.

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

    To make consumption easier for projects that don't do heavy substitution,
    [--unbind-item-vars] changes the variables bound at the top-level (i.e. in
    the [GenericParams] of items) to be [Free]. The example above becomes:
    {@rust[
      fn f<'a, 'b>(x: for<'c> fn(&'b u8, &'c u16, for<'d> fn(&'b u32, &'c u64, &'d u128)) -> u64) {}
           ^^^^^^         ^^       ^       ^          ^^       ^        ^        ^
             |       inner binder  |       |     inner binder  |        |        |
       top-level binder            |       |                   |        |        |
                                Free(b)    |                Free(b)     |     Bound(0, d)
                                           |                            |
                                       Bound(0, c)                 Bound(1, c)
    ]} *)
and 'a0 de_bruijn_var =
  | Bound of de_bruijn_id * 'a0
      (** A variable attached to the nth binder, counting from the innermost. *)
  | Free of 'a0
      (** A variable attached to the outermost binder (the one on the item).
          This is not used within Charon itself, instead ewe insert it at the
          end if [--unbind-item-vars] is set. *)

and trait_clause_id = (TraitClauseId.id[@visitors.opaque])

and type_var_id = (TypeVarId.id[@visitors.opaque])
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_type_vars";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_scalar" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_type_vars";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_scalar" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "reduce_type_vars";
      monomorphic = [ "env" ];
      variety = "reduce";
      ancestors = [ "reduce_scalar" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "mapreduce_type_vars";
      monomorphic = [ "env" ];
      variety = "mapreduce";
      ancestors = [ "mapreduce_scalar" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

let rec hash_de_bruijn_id : de_bruijn_id -> int =
 fun (x : de_bruijn_id) -> HashBasic.hash_int x

and hash_de_bruijn_var : 'a0. ('a0 -> int) -> 'a0 de_bruijn_var -> int =
 fun hash_a0 (x : _ de_bruijn_var) ->
  match x with
  | Bound (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 0 (hash_de_bruijn_id x0))
        (hash_a0 x1)
  | Free x0 -> HashBasic.combine 1 (hash_a0 x0)

and hash_trait_clause_id : trait_clause_id -> int =
 fun (x : trait_clause_id) -> TraitClauseId.hash_id x

and hash_type_var_id : type_var_id -> int =
 fun (x : type_var_id) -> TypeVarId.hash_id x

class ['self] iter_ty_base =
  object (self : 'self)
    inherit [_] iter_type_vars

    method visit_range_inclusive :
        'a. ('env -> 'a -> unit) -> 'env -> 'a range_inclusive -> unit =
      fun visit_elem env (x, y) ->
        visit_elem env x;
        visit_elem env y

    method visit_assoc_type_id_map :
        'a. ('env -> 'a -> unit) -> 'env -> 'a assoc_type_id_map -> unit =
      AssocTypeId.Map.visit_iter

    method visit_assoc_const_id_map :
        'a. ('env -> 'a -> unit) -> 'env -> 'a assoc_const_id_map -> unit =
      AssocConstId.Map.visit_iter
  end

class ['self] map_ty_base =
  object (self : 'self)
    inherit [_] map_type_vars

    method visit_range_inclusive :
        'a 'b.
        ('env -> 'a -> 'b) -> 'env -> 'a range_inclusive -> 'b range_inclusive =
      fun visit_elem env (x, y) -> (visit_elem env x, visit_elem env y)

    method visit_assoc_type_id_map :
        'a 'b.
        ('env -> 'a -> 'b) ->
        'env ->
        'a assoc_type_id_map ->
        'b assoc_type_id_map =
      AssocTypeId.Map.visit_map

    method visit_assoc_const_id_map :
        'a 'b.
        ('env -> 'a -> 'b) ->
        'env ->
        'a assoc_const_id_map ->
        'b assoc_const_id_map =
      AssocConstId.Map.visit_map
  end

type abi =
  | AbiRust
  | AbiC
  | AbiOther of string
      (** Rust's spelling for the ABI, e.g. "C-unwind" or "system". *)

(** A value of type [T] bound by generic parameters. Used in any context where
    we're adding generic parameters that aren't on the top-level item, e.g.
    [for<'a>] clauses (uses [RegionBinder] for now), trait methods, GATs (TODO).
*)
and 'a0 binder = {
  binder_params : generic_params;
  binder_value : 'a0;
      (** Named this way to highlight accesses to the inner value that might be
          handling parameters incorrectly. Prefer using helper methods. *)
}

and binder_kind =
  | BKTraitType of trait_decl_id * assoc_type_id
      (** The parameters of a generic associated type. *)
  | BKTraitMethod of trait_decl_id * trait_method_id
      (** The parameters of a trait method. Used in the [methods] lists in trait
          decls and trait impls. *)
  | BKInherentImplBlock
      (** The parameters bound in a non-trait [impl] block. Used in the [Name]s
          of inherent methods. *)
  | BKDyn  (** Binder used for [dyn Trait] existential predicates. *)
  | BKOther  (** Some other use of a binder outside the main Charon ast. *)

(** Builtin ADT identifiers. *)
and builtin_adt =
  | TTuple  (** A tuple [(A, B, ...)], including [unit]. *)
  | TBox
      (** Boxes; always detected, though they are only treated as primitives
          with [--treat-box-as-builtin] *)
  | TStr
      (** The [str] type, which corresponds to a [[u8]] that encodes a string
          with UTF-8. *)

(** Describes a built-in impl. Mostly lists the implemented trait, sometimes
    with more details about the contents of the implementation. *)
and builtin_impl_data =
  | BuiltinAuto
      (** Auto traits (defined with [auto trait ...], also [Unpin]). *)
  | BuiltinSized
  | BuiltinMetaSized
  | BuiltinPointeeSized
  | BuiltinCopy
  | BuiltinClone
  | BuiltinTuple
  | BuiltinTransmute
  | BuiltinUnsize
  | BuiltinPointee
  | BuiltinDiscriminantKind
  | BuiltinFn
  | BuiltinFnMut
  | BuiltinFnOnce
  | BuiltinFnPtr
  | BuiltinAsyncFn
  | BuiltinAsyncFnMut
  | BuiltinAsyncFnOnce
  | BuiltinCoroutine
  | BuiltinFuture
  | BuiltinTryAsDynCompatible
      (** Auto-trait used for [try_as_dyn] (see
          https://github.com/rust-lang/rust/issues/144361) *)
  | BuiltinNoopDestruct
      (** An impl of [Destruct] for a type with no drop glue. *)
  | BuiltinUntrackedDestruct
      (** An impl of [Destruct] for a type parameter, which we could not resolve
          because [--add-drop-bounds] was not set. *)
  | BuiltinRemovedAdtClause
      (** Placeholder used by the [--remove-adt-clauses] pass when it strips a
          trait clause from a type declaration. References to the removed clause
          are rewritten as
          [BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }]. *)

(** A byte, in the MiniRust sense: it can either be uninitialized, a concrete u8
    value, or part of a pointer with provenance (e.g. to a global or a function)
*)
and byte =
  | Uninit  (** An uninitialized byte *)
  | Value of int  (** A concrete byte value *)
  | Provenance of provenance * int
      (** A byte that is part of a pointer with provenance. The u8 is the offset
          within the pointer. Note that we do not have an actual value for this
          pointer byte, unlike MiniRust, as that is non-deterministic. *)

(** A const generic variable in a signature or binder. *)
and const_generic_param = {
  index : const_generic_var_id;
      (** Index identifying the variable among other variables bound at the same
          level. *)
  name : string;  (** Const generic name *)
  ty : ty;  (** Type of the const generic *)
}

and const_generic_var_id = (ConstGenericVarId.id[@visitors.opaque])

(** A constant expression. *)
and constant_expr = { kind : constant_expr_kind; ty : ty }

and constant_expr_kind =
  | CBool of bool  (** Boolean value. *)
  | CInteger of integer_value  (** Integer value. *)
  | CChar of char_value  (** Char value. *)
  | CFloat of float_value  (** Float value. *)
  | CAdt of variant_id option * constant_expr list
      (** Value of an ADT (struct or enum).

          This is eliminated inside functions if [--raw-consts] is off. *)
  | CArray of constant_expr list
      (** Array value.

          This is eliminated inside functions if [--raw-consts] is off. *)
  | CRef of constant_expr * unsizing_metadata option
      (** A shared reference to a constant value.

          This is eliminated inside functions if [--raw-consts] is off. *)
  | CPtr of ref_kind * constant_expr * unsizing_metadata option
      (** A pointer to a static.

          This is eliminated inside functions if [--raw-consts] is off. *)
  | CStr of string  (** [str] value. *)
  | CByteStr of int list  (** Byte string value. *)
  | CFnDef of fn_ptr
      (** ZST constant corresponding to the unique value of the type of a
          function item. *)
  | CFnPtr of fn_ptr
      (** A function pointer value; this is a pointer (i.e. an address).

          This is eliminated inside functions if [--raw-consts] is off. *)
  | CCast of constant_expr * ty
      (** Cast a constant value to another type (e.g. erase a vtable method
          pointer to [*const ()]). *)
  | CPtrNoProvenance of big_int
      (** A pointer with no provenance (e.g. 0 for the null pointer)

          This is eliminated inside functions if [--raw-consts] is off. *)
  | CTypeId of ty  (** The [TypeId] value for a type. *)
  | CRawMemory of byte list
      (** Raw memory value obtained from constant evaluation. Used when a more
          structured representation isn't possible (e.g. for unions) or just
          isn't implemented yet. *)
  | CVar of const_generic_var_id de_bruijn_var  (** A const generic var *)
  | CGlobal of global_decl_ref
      (** The value of a constant/static.

          This is eliminated inside functions if [--raw-consts] is off. *)
  | CCall of fn_ptr * constant_expr list  (** A call to a [const fn]. *)
  | CTraitConst of trait_ref * assoc_const_id
      (** A trait associated constant.

          E.g.:
          {@rust[
            impl Foo for Bar {
              const C : usize = 32; // <-
            }
          ]} *)
  | CVTableRef of poly_trait_ref
      (** A reference to the vtable [static] item for this trait ref. This can
          be normalized if we emitted a vtable item.

          This is eliminated if [--raw-consts] is off. *)
  | CDiscriminant of type_decl_ref * variant_id
      (** The integer discriminant value corresponding to this enum variant. *)
  | CSizeOf of ty  (** The size of the given type. *)
  | CAlignOf of ty  (** The alignment of the given type. *)
  | COffsetOf of type_decl_ref * variant_id option * field_id
      (** The offset of the given field. *)
  | COpaque of string
      (** A constant expression that Charon doesn't handle, along with the
          reason why. *)

(** The contents of a [dyn Trait] type. *)
and dyn_predicate = {
  binder : ty binder;
      (** This binder binds a single type [T], which is considered existentially
          quantified. The predicates in the binder apply to [T] and represent
          the [dyn Trait] constraints. E.g. [dyn Iterator<Item=u32> + Send] is
          represented as [exists<T: Iterator<Item=u32> + Send> T].

          Only the first trait clause may have methods. We use the vtable of
          this trait in the [dyn Trait] pointer metadata. *)
}

and field_id = (FieldId.id[@visitors.opaque])

(** Reference to a function, possibly indirected via a trait. *)
and fn_ptr = { kind : fn_ptr_kind; generics : generic_args }

and fn_ptr_kind =
  | Fun of fun_decl_id
  | TraitMethod of trait_ref * trait_method_id
      (** If a trait: the reference to the trait and the id of the trait method.
      *)

(** Reference to a function declaration. *)
and fun_decl_ref = {
  id : fun_decl_id;
  generics : generic_args;  (** Generic arguments passed to the function. *)
}

(** A function signature. *)
and fun_sig = {
  is_unsafe : bool;  (** Is the function unsafe or not *)
  abi : abi;  (** The calling convention of this function. *)
  is_variadic : bool;
      (** Whether this is a C-variadic function (its last parameter is [...]).
      *)
  inputs : ty list;
  output : ty;
}

(** A set of generic arguments. *)
and generic_args = {
  regions : region list;
  types : ty list;
  const_generics : constant_expr list;
  trait_refs : poly_trait_ref list;
}

(** Generic parameters for a declaration, including predicates. *)
and generic_params = {
  regions : region_param list;
  types : type_param list;
  const_generics : const_generic_param list;
  trait_clauses : trait_param list;
  regions_outlive : (region, region) outlives_pred region_binder list;
      (** The first region in the pair outlives the second region *)
  types_outlive : (ty, region) outlives_pred region_binder list;
      (** The type outlives the region *)
  trait_type_constraints : trait_type_constraint region_binder list;
      (** Constraints over trait associated types *)
}

(** Reference to a global declaration. *)
and global_decl_ref = { id : global_decl_id; generics : generic_args }

(** Hash-consed data structure: a reference-counted wrapper that guarantees that
    two equal value will be stored at the same address. This makes it possible
    to use the pointer address as a hash value. *)
and 'a0 hash_consed = 'a0 (* Not actually hash-consed on the OCaml side *)

(** The nature of locations where a given lifetime parameter is used. If this
    lifetime ever flows to be used as the lifetime of a mutable reference
    [&'a mut] then we consider it mutable. *)
and lifetime_mutability =
  | LtMutable  (** A lifetime that is used for a mutable reference. *)
  | LtShared  (** A lifetime used only in shared references. *)
  | LtUnknown
      (** A lifetime for which we couldn't/didn't compute mutability. *)

(** .0 outlives .1 *)
and ('a0, 'a1) outlives_pred = 'a0 * 'a1

(** A proof of a higher-ranked trait predicate. *)
and poly_trait_ref = trait_ref region_binder

(** Where a given predicate came from. *)
and predicate_origin =
  | WhereClauseOnFn
  | WhereClauseOnType
  | WhereClauseOnImpl
  | TraitSelf
  | WhereClauseOnTrait
  | TraitItem of assoc_type_id
  | OriginDyn  (** Clauses that are part of a [dyn Trait] type. *)

and provenance =
  | ProvGlobal of global_decl_ref
  | ProvFunction of fn_ptr
  | ProvUnknown

and ref_kind = RMut | RShared

and region =
  | RVar of region_id de_bruijn_var
      (** Region variable. See [DeBruijnVar] for details. *)
  | RStatic  (** Static region *)
  | RBody of region_id
      (** Body-local region, considered existentially-bound at the level of a
          body. *)
  | RErased  (** Erased region *)

(** Region arguments used to instantiate a [[RegionBinder]]. *)
and region_args = { regions : region list }

(** A value of type [T] bound by regions. We should use [binder] instead but
    this causes name clash issues in the derived ocaml visitors. *)
and 'a0 region_binder = {
  binder_regions : region_param list;
  regions_outlive : (region, region) outlives_pred region_binder list;
      (** Outlives relations involving the bound regions. *)
  types_outlive : (ty, region) outlives_pred region_binder list;
      (** Outlives relations involving the bound regions. *)
  binder_value : 'a0;
      (** Named this way to highlight accesses to the inner value that might be
          handling parameters incorrectly. Prefer using helper methods. *)
}

and region_id = (RegionId.id[@visitors.opaque])

(** A region variable in a signature or binder. *)
and region_param = {
  index : region_id;
      (** Index identifying the variable among other variables bound at the same
          level. *)
  name : string option;  (** Region name *)
  variance : variance;  (** Variance of this parameter. *)
  mutability : lifetime_mutability;
      (** Whether this lifetime is (recursively) used in a [&'a mut T] type.
          Only [true] if this lifetime parameter belongs to an ADT. This is a
          global analysis that looks even into opaque items. When unsure, err on
          the side of assuming mutability. *)
}

(** The value of a trait associated type. *)
and trait_assoc_ty_impl = {
  value : ty;
  implied_trait_refs : poly_trait_ref list;
      (** This matches the corresponding vector in [TraitAssocTy]. In the same
          way, this is empty after the [lift_associated_item_clauses] pass. *)
}

(** A predicate of the form [Type: Trait<Args>].

    About the generics, if we write:
    {@rust[
      impl Foo<bool> for String { ... }
    ]}

    The substitution is: [[String, bool]]. *)
and trait_decl_ref = { id : trait_decl_id; generics : generic_args }

(** A reference to a tait impl, using the provided arguments. *)
and trait_impl_ref = { id : trait_impl_id; generics : generic_args }

(** A trait predicate in a signature, of the form [Type: Trait<Args>]. This
    functions like a variable binder, to which variables of the form
    [TraitRefKind::Clause] can refer to. *)
and trait_param = {
  clause_id : trait_clause_id;
      (** Index identifying the clause among other clauses bound at the same
          level. *)
  span : span option;
  origin : predicate_origin;
      (** Where the predicate was written, relative to the item that requires
          it. *)
  trait : trait_decl_ref region_binder;  (** The trait that is implemented. *)
}

(** A proof of a trait predicate.

    This type is hash-consed, [TraitRefContents] contains the actual data. *)
and trait_ref = trait_ref_contents hash_consed

and trait_ref_contents = {
  kind : trait_ref_kind;
  trait_decl_ref : trait_decl_ref;
      (** The predicate that is proven by that trait proof. *)
}

(** Identifier of a trait instance. This is derived from the trait resolution.

    Should be read as a path inside the trait clauses which apply to the current
    definition. Note that every path designated by [TraitInstanceId] refers to a
    *trait instance*, which is why the [[TraitRefKind::Clause]] variant may seem
    redundant with some of the other variants. *)
and trait_ref_kind =
  | TraitImpl of trait_impl_ref
      (** A specific top-level implementation item. *)
  | Clause of trait_clause_id de_bruijn_var * region_args
      (** One of the local clauses, instantiated with the given region
          arguments.

          Example:
          {@rust[
            fn f<T>(...) where T : Foo
                               ^^^^^^^
                               Clause(0)
          ]} *)
  | ParentClause of trait_ref * trait_clause_id * region_args
      (** A parent clause

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
              Parent(Clause(0), 1)::f(x)
                                ^
                                parent clause 1 of clause 0
            }
          ]} *)
  | ItemClause of
      trait_ref * assoc_type_id * generic_args * trait_clause_id * region_args
      (** A clause defined on an associated type.

          Example:
          {@rust[
            trait Foo {
              type W<X>: Bar0 + Bar1 // Bar1 contains a method bar1
                                ^^^^
                          this is the clause 1 applying to W
            }

            fn f<T: Foo>(x : T::W<u32>) {
              x.bar1();
              ^^^^^^
              ItemClause {
                  trait_ref: Clause(0), // start with the [T: Foo] clause
                  type_id: W, // look at the item [W]
                  generics: [u32], // with these args
                  clause_id: 1, // and take the clause 1 of this item
                  clause_args: [],
              }
            }
          ]}

          For associated types without arguments, we turn such clauses into
          parent clauses of the trait, in the [lift_associated_item_clauses]
          pass.

          Fields:
          - [trait_ref]
          - [type_id]
          - [generics]: Generic arguments for the associated type.
          - [clause_id]: Id of the clause among those for this item.
          - [clause_args]: Region arguments that instantiate the higher-ranked
            item clause. *)
  | Self
      (** The implicit [Self: Trait] clause. Present inside trait declarations,
          including trait method declarations. Not present in trait
          implementations as we can use [TraitImpl] intead. *)
  | BuiltinOrAuto of
      builtin_impl_data
      * poly_trait_ref list
      * trait_assoc_ty_impl assoc_type_id_map
      * global_decl_ref option
      (** A trait implementation that is computed by the compiler, such as for
          built-in trait [Sized]. This morally points to an invisible [impl]
          block; as such it contains the information we may need from one.

          Also used as a placeholder for trait clauses that were stripped by the
          [--remove-adt-clauses] pass: the original [Clause] reference is
          replaced with a
          [BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }]. See
          [[BuiltinImplData::RemovedAdtClause]].

          Fields:
          - [builtin_data]: Metadata that identifies this impl.
          - [parent_trait_refs]: Exactly like the same field on [TraitImpl]: the
            [TraitRef]s required to satisfy the implied predicates on the trait
            declaration. E.g. since [FnMut: FnOnce], a built-in [T: FnMut] impl
            would have a [TraitRef] for [T: FnOnce].
          - [types]: The values of the associated types for this trait.
          - [vtable]: The vtable value for this builtin implementation, if we
            generated one. *)
  | Dyn  (** The automatically-generated implementation for [dyn Trait]. *)
  | UnknownTrait of string  (** For error reporting. *)

(** A constraint over a trait associated type.

    Example:
    {@rust[
      T : Foo<S = String>
              ^^^^^^^^^^
    ]} *)
and trait_type_constraint = {
  trait_ref : trait_ref;
  type_id : assoc_type_id;
  ty : ty;
}

(** A type.

    This is an interned value; see [TyKind] for the actual contents. *)
and ty = ty_kind hash_consed

(** A type.

    This is interned as [Ty], making it cheap to clone and compare. *)
and ty_kind =
  | TScalar of scalar_type
      (** A scalar (integers, floats, [char], or [bool]). *)
  | TArray of ty * constant_expr * trait_ref option
      (** An array [[T; N]]. The third field is the proof that [T: Sized]; it is
          absent with [--hide-marker-traits]. *)
  | TSlice of ty * trait_ref option
      (** A slice [[T]]. The second field is the proof that [T: Sized]; it is
          absent with [--hide-marker-traits]. *)
  | TAdt of type_decl_ref
      (** An ADT: structs, enums, unions, as well as tuples and [str]. *)
  | TRef of region * ty * ref_kind  (** A reference: [&T] or [&mut T]. *)
  | TRawPtr of ty * ref_kind  (** A raw pointer. *)
  | TFnDef of fn_ptr region_binder
      (** The unique type associated with each function item. Each function item
          is given a unique type that has the function's early-bound generics.
          This type is not generally nameable in Rust; it's a ZST (there's a
          unique value), and a value of that type can be cast to a function
          pointer or passed to functions that expect [FnOnce]/[FnMut]/[Fn]
          parameters.

          There's a binder here because charon function items take both early
          and late-bound lifetimes as arguments; given that the type we're
          pointing to is polymorphic in the late-bound variables, we need to
          bind them here.

          {@rust[
            rust
            // ['a] is early-bound, 'b is late-bound.
            fn foo<'a, 'b>(x: &'a u32, y: &'b u32)
            where u32: 'b
            {}
          ]}
          For rustc, there's a ZST [foo<'a>], that can be cast to a
          [for<'b> fn(&'a u32, &'b u32)] function pointer. For charon, there's
          an item [foo<'a, 'b>], and the [FnDef] item that corresponds to
          rustc's [foo<'a>] is represented as [FnDef(for<'b> foo<'a, 'b>)]. *)
  | TFnPtr of fun_sig region_binder
      (** Function pointer type. This is a literal pointer to a region of memory
          that contains a callable function.

          A function pointer can have lifetime generics, e.g.
          [for<'a> fn(&'a mut u32) -> &'a u32], hence the binder. *)
  | TDynTrait of dyn_predicate
      (** [dyn Trait]: erased value known to implement [Trait]. A pointer to it
          will carry a vtable pointer that stores the methods that can be called
          on this value. *)
  | TPattern of ty * type_pattern
      (** A pattern type: a type that is representationally identical to its
          base type, except the only valid values are the ones that match the
          pattern. *)
  | TNever  (** The never type, the canonical uninhabited type. *)
  | TVar of type_var_id de_bruijn_var  (** A type variable. *)
  | TTraitType of trait_ref * assoc_type_id * generic_args
      (** A trait associated type: [<T as Trait>::AssocType<Args>]. *)
  | TPtrMetadata of ty
      (** The type of pointer metadata for the given type; e.g. for [[T]], this
          type is [usize]. The way to write this type in Rust is
          [<X as core::ptr::Pointee>::Metadata]. *)
  | TError of string  (** A type that could not be computed or was incorrect. *)

(** Reference to a type declaration.

    This includes user-defined ADTs (structs, enums, unions), but also tuples,
    boxes, and [str], which we translate as [struct str([u8])]. *)
and type_decl_ref = {
  id : type_decl_id;
  generics : generic_args;
  builtin : builtin_adt option;
      (** If this points to a builtin ADT, it is recorded here for easier
          identification. *)
}

(** A type variable in a signature or binder. *)
and type_param = {
  index : type_var_id;
      (** Index identifying the variable among other variables bound at the same
          level. *)
  name : string;  (** Variable name *)
  variance : variance;  (** Variance of this parameter. *)
}

(** A type-level pattern used by [[TyKind::Pattern]]. *)
and type_pattern =
  | Range of constant_expr * constant_expr
  | OrPattern of type_pattern list
  | NotNull

and unsizing_metadata =
  | MetaLength of constant_expr  (** Cast from [[T; N]] to [[T]]. *)
  | MetaVTable of poly_trait_ref * constant_expr
      (** Cast from a sized value to a [dyn Trait] value. The [TraitRef] is the
          proof of the [dyn Trait] predicate; the constant expression is a
          reference to the vtable [static] value. *)
  | MetaVTableUpcast of field_id list
      (** Cast from [dyn Trait] to [dyn OtherTrait]. The fields indicate how to
          retreive the vtable: it's always either the same we already had, or
          the vtable for a (possibly nested) supertrait.

          Note that we cheat in one case: when upcasting to a marker trait (e.g.
          [dyn Trait -> dyn Sized]), we keep the current vtable. *)
  | MetaUnknown

(** The variance of a lifetime or type parameter. *)
and variance =
  | Covariant
  | Invariant
  | Contravariant
  | Bivariant
  | VaUnknown
      (** Variance was not sensible (e.g. on impls), not available (e.g. on
          higher-kinded predicates), or not computed (e.g. on parameters that
          Charon invents). *)

and variant_id = (VariantId.id[@visitors.opaque])
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_ty";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_ty_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_ty";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_ty_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

let rec hash_abi : abi -> int =
 fun (x : abi) ->
  match x with
  | AbiRust -> 0
  | AbiC -> 1
  | AbiOther x0 -> HashBasic.combine 2 (HashBasic.hash_string x0)

and hash_binder : 'a0. ('a0 -> int) -> 'a0 binder -> int =
 fun hash_a0 (x : _ binder) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_generic_params x.binder_params))
    (hash_a0 x.binder_value)

and hash_binder_kind : binder_kind -> int =
 fun (x : binder_kind) ->
  match x with
  | BKTraitType (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 0 (hash_trait_decl_id x0))
        (hash_assoc_type_id x1)
  | BKTraitMethod (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 1 (hash_trait_decl_id x0))
        (hash_trait_method_id x1)
  | BKInherentImplBlock -> 2
  | BKDyn -> 3
  | BKOther -> 4

and hash_builtin_adt : builtin_adt -> int =
 fun (x : builtin_adt) ->
  match x with
  | TTuple -> 0
  | TBox -> 1
  | TStr -> 2

and hash_builtin_impl_data : builtin_impl_data -> int =
 fun (x : builtin_impl_data) ->
  match x with
  | BuiltinAuto -> 0
  | BuiltinSized -> 1
  | BuiltinMetaSized -> 2
  | BuiltinPointeeSized -> 3
  | BuiltinCopy -> 4
  | BuiltinClone -> 5
  | BuiltinTuple -> 6
  | BuiltinTransmute -> 7
  | BuiltinUnsize -> 8
  | BuiltinPointee -> 9
  | BuiltinDiscriminantKind -> 10
  | BuiltinFn -> 11
  | BuiltinFnMut -> 12
  | BuiltinFnOnce -> 13
  | BuiltinFnPtr -> 14
  | BuiltinAsyncFn -> 15
  | BuiltinAsyncFnMut -> 16
  | BuiltinAsyncFnOnce -> 17
  | BuiltinCoroutine -> 18
  | BuiltinFuture -> 19
  | BuiltinTryAsDynCompatible -> 20
  | BuiltinNoopDestruct -> 21
  | BuiltinUntrackedDestruct -> 22
  | BuiltinRemovedAdtClause -> 23

and hash_byte : byte -> int =
 fun (x : byte) ->
  match x with
  | Uninit -> 0
  | Value x0 -> HashBasic.combine 1 (HashBasic.hash_int x0)
  | Provenance (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 2 (hash_provenance x0))
        (HashBasic.hash_int x1)

and hash_const_generic_param : const_generic_param -> int =
 fun (x : const_generic_param) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_const_generic_var_id x.index))
       (HashBasic.hash_string x.name))
    (hash_ty x.ty)

and hash_const_generic_var_id : const_generic_var_id -> int =
 fun (x : const_generic_var_id) -> ConstGenericVarId.hash_id x

and hash_constant_expr : constant_expr -> int =
 fun (x : constant_expr) ->
  HashBasic.combine (hash_constant_expr_kind x.kind) (hash_ty x.ty)

and hash_constant_expr_kind : constant_expr_kind -> int =
 fun (x : constant_expr_kind) ->
  match x with
  | CBool x0 -> HashBasic.combine 0 (HashBasic.hash_bool x0)
  | CInteger x0 -> HashBasic.combine 1 (hash_integer_value x0)
  | CChar x0 -> HashBasic.combine 2 (hash_char_value x0)
  | CFloat x0 -> HashBasic.combine 3 (hash_float_value x0)
  | CAdt (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 4 ((HashBasic.hash_option hash_variant_id) x0))
        ((HashBasic.hash_list hash_constant_expr) x1)
  | CArray x0 ->
      HashBasic.combine 5 ((HashBasic.hash_list hash_constant_expr) x0)
  | CRef (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 6 (hash_constant_expr x0))
        ((HashBasic.hash_option hash_unsizing_metadata) x1)
  | CPtr (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 7 (hash_ref_kind x0))
           (hash_constant_expr x1))
        ((HashBasic.hash_option hash_unsizing_metadata) x2)
  | CStr x0 -> HashBasic.combine 8 (HashBasic.hash_string x0)
  | CByteStr x0 ->
      HashBasic.combine 9 ((HashBasic.hash_list HashBasic.hash_int) x0)
  | CFnDef x0 -> HashBasic.combine 10 (hash_fn_ptr x0)
  | CFnPtr x0 -> HashBasic.combine 11 (hash_fn_ptr x0)
  | CCast (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 12 (hash_constant_expr x0))
        (hash_ty x1)
  | CPtrNoProvenance x0 -> HashBasic.combine 13 (hash_big_int x0)
  | CTypeId x0 -> HashBasic.combine 14 (hash_ty x0)
  | CRawMemory x0 -> HashBasic.combine 15 ((HashBasic.hash_list hash_byte) x0)
  | CVar x0 ->
      HashBasic.combine 16 ((hash_de_bruijn_var hash_const_generic_var_id) x0)
  | CGlobal x0 -> HashBasic.combine 17 (hash_global_decl_ref x0)
  | CCall (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 18 (hash_fn_ptr x0))
        ((HashBasic.hash_list hash_constant_expr) x1)
  | CTraitConst (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 19 (hash_trait_ref x0))
        (hash_assoc_const_id x1)
  | CVTableRef x0 -> HashBasic.combine 20 (hash_trait_ref x0)
  | CDiscriminant (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 21 (hash_type_decl_ref x0))
        (hash_variant_id x1)
  | CSizeOf x0 -> HashBasic.combine 22 (hash_ty x0)
  | CAlignOf x0 -> HashBasic.combine 23 (hash_ty x0)
  | COffsetOf (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 24 (hash_type_decl_ref x0))
           ((HashBasic.hash_option hash_variant_id) x1))
        (hash_field_id x2)
  | COpaque x0 -> HashBasic.combine 25 (HashBasic.hash_string x0)

and hash_dyn_predicate : dyn_predicate -> int =
 fun (x : dyn_predicate) -> HashBasic.combine 0 ((hash_binder hash_ty) x.binder)

and hash_field_id : field_id -> int = fun (x : field_id) -> FieldId.hash_id x

and hash_fn_ptr : fn_ptr -> int =
 fun (x : fn_ptr) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_fn_ptr_kind x.kind))
    (hash_generic_args x.generics)

and hash_fn_ptr_kind : fn_ptr_kind -> int =
 fun (x : fn_ptr_kind) ->
  match x with
  | Fun x0 -> HashBasic.combine 0 (hash_fun_decl_id x0)
  | TraitMethod (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 1 (hash_trait_ref x0))
        (hash_trait_method_id x1)

and hash_fun_decl_ref : fun_decl_ref -> int =
 fun (x : fun_decl_ref) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_fun_decl_id x.id))
    (hash_generic_args x.generics)

and hash_fun_sig : fun_sig -> int =
 fun (x : fun_sig) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine 0 (HashBasic.hash_bool x.is_unsafe))
             (hash_abi x.abi))
          (HashBasic.hash_bool x.is_variadic))
       ((HashBasic.hash_list hash_ty) x.inputs))
    (hash_ty x.output)

and hash_generic_args : generic_args -> int =
 fun (x : generic_args) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine 0 ((HashBasic.hash_list hash_region) x.regions))
          ((HashBasic.hash_list hash_ty) x.types))
       ((HashBasic.hash_list hash_constant_expr) x.const_generics))
    ((HashBasic.hash_list hash_trait_ref) x.trait_refs)

and hash_generic_params : generic_params -> int =
 fun (x : generic_params) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine
                (HashBasic.combine
                   (HashBasic.combine 0
                      ((HashBasic.hash_list hash_region_param) x.regions))
                   ((HashBasic.hash_list hash_type_param) x.types))
                ((HashBasic.hash_list hash_const_generic_param)
                   x.const_generics))
             ((HashBasic.hash_list hash_trait_param) x.trait_clauses))
          ((HashBasic.hash_list
              (hash_region_binder (hash_outlives_pred hash_region hash_region)))
             x.regions_outlive))
       ((HashBasic.hash_list
           (hash_region_binder (hash_outlives_pred hash_ty hash_region)))
          x.types_outlive))
    ((HashBasic.hash_list (hash_region_binder hash_trait_type_constraint))
       x.trait_type_constraints)

and hash_global_decl_ref : global_decl_ref -> int =
 fun (x : global_decl_ref) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_global_decl_id x.id))
    (hash_generic_args x.generics)

and hash_hash_consed : 'a0. ('a0 -> int) -> 'a0 hash_consed -> int =
 fun hash_a0 (x : _ hash_consed) -> hash_a0 x

and hash_lifetime_mutability : lifetime_mutability -> int =
 fun (x : lifetime_mutability) ->
  match x with
  | LtMutable -> 0
  | LtShared -> 1
  | LtUnknown -> 2

and hash_outlives_pred :
    'a0 'a1. ('a0 -> int) -> ('a1 -> int) -> ('a0, 'a1) outlives_pred -> int =
 fun hash_a0 hash_a1 (x : (_, _) outlives_pred) ->
  let x0, x1 = x in
  HashBasic.combine (HashBasic.combine 0 (hash_a0 x0)) (hash_a1 x1)

and hash_predicate_origin : predicate_origin -> int =
 fun (x : predicate_origin) ->
  match x with
  | WhereClauseOnFn -> 0
  | WhereClauseOnType -> 1
  | WhereClauseOnImpl -> 2
  | TraitSelf -> 3
  | WhereClauseOnTrait -> 4
  | TraitItem x0 -> HashBasic.combine 5 (hash_assoc_type_id x0)
  | OriginDyn -> 6

and hash_provenance : provenance -> int =
 fun (x : provenance) ->
  match x with
  | ProvGlobal x0 -> HashBasic.combine 0 (hash_global_decl_ref x0)
  | ProvFunction x0 -> HashBasic.combine 1 (hash_fn_ptr x0)
  | ProvUnknown -> 2

and hash_ref_kind : ref_kind -> int =
 fun (x : ref_kind) ->
  match x with
  | RMut -> 0
  | RShared -> 1

and hash_region : region -> int =
 fun (x : region) ->
  match x with
  | RVar x0 -> HashBasic.combine 0 ((hash_de_bruijn_var hash_region_id) x0)
  | RStatic -> 1
  | RBody x0 -> HashBasic.combine 2 (hash_region_id x0)
  | RErased -> 3

and hash_region_binder : 'a0. ('a0 -> int) -> 'a0 region_binder -> int =
 fun hash_a0 (x : _ region_binder) ->
  HashBasic.combine
    (HashBasic.combine 0
       ((HashBasic.hash_list hash_region_param) x.binder_regions))
    (hash_a0 x.binder_value)

and hash_region_id : region_id -> int =
 fun (x : region_id) -> RegionId.hash_id x

and hash_region_param : region_param -> int =
 fun (x : region_param) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine 0 (hash_region_id x.index))
          ((HashBasic.hash_option HashBasic.hash_string) x.name))
       (hash_variance x.variance))
    (hash_lifetime_mutability x.mutability)

and hash_trait_assoc_ty_impl : trait_assoc_ty_impl -> int =
 fun (x : trait_assoc_ty_impl) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_ty x.value))
    ((HashBasic.hash_list hash_trait_ref) x.implied_trait_refs)

and hash_trait_decl_ref : trait_decl_ref -> int =
 fun (x : trait_decl_ref) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_trait_decl_id x.id))
    (hash_generic_args x.generics)

and hash_trait_impl_ref : trait_impl_ref -> int =
 fun (x : trait_impl_ref) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_trait_impl_id x.id))
    (hash_generic_args x.generics)

and hash_trait_param : trait_param -> int =
 fun (x : trait_param) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine 0 (hash_trait_clause_id x.clause_id))
          ((HashBasic.hash_option hash_span) x.span))
       (hash_predicate_origin x.origin))
    ((hash_region_binder hash_trait_decl_ref) x.trait)

and hash_trait_ref : trait_ref -> int =
 fun (x : trait_ref) -> (hash_hash_consed hash_trait_ref_contents) x

and hash_trait_ref_contents : trait_ref_contents -> int =
 fun (x : trait_ref_contents) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_trait_ref_kind x.kind))
    ((hash_region_binder hash_trait_decl_ref) x.trait_decl_ref)

and hash_trait_ref_kind : trait_ref_kind -> int =
 fun (x : trait_ref_kind) ->
  match x with
  | TraitImpl x0 -> HashBasic.combine 0 (hash_trait_impl_ref x0)
  | Clause x0 ->
      HashBasic.combine 1 ((hash_de_bruijn_var hash_trait_clause_id) x0)
  | ParentClause (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 2 (hash_trait_ref x0))
        (hash_trait_clause_id x1)
  | ItemClause (x0, x1, x2, x3) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine
              (HashBasic.combine 3 (hash_trait_ref x0))
              (hash_assoc_type_id x1))
           (hash_generic_args x2))
        (hash_trait_clause_id x3)
  | Self -> 4
  | BuiltinOrAuto (x0, x1, x2, x3) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine
              (HashBasic.combine 5 (hash_builtin_impl_data x0))
              ((HashBasic.hash_list hash_trait_ref) x1))
           ((hash_assoc_type_id_map hash_trait_assoc_ty_impl) x2))
        ((HashBasic.hash_option hash_global_decl_ref) x3)
  | Dyn -> 6
  | UnknownTrait x0 -> HashBasic.combine 7 (HashBasic.hash_string x0)

and hash_trait_type_constraint : trait_type_constraint -> int =
 fun (x : trait_type_constraint) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_trait_ref x.trait_ref))
       (hash_assoc_type_id x.type_id))
    (hash_ty x.ty)

and hash_ty : ty -> int = fun (x : ty) -> (hash_hash_consed hash_ty_kind) x

and hash_ty_kind : ty_kind -> int =
 fun (x : ty_kind) ->
  match x with
  | TScalar x0 -> HashBasic.combine 0 (hash_scalar_type x0)
  | TArray (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 1 (hash_ty x0))
           (hash_constant_expr x1))
        ((HashBasic.hash_option hash_trait_ref) x2)
  | TSlice (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 2 (hash_ty x0))
        ((HashBasic.hash_option hash_trait_ref) x1)
  | TAdt x0 -> HashBasic.combine 3 (hash_type_decl_ref x0)
  | TRef (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine (HashBasic.combine 4 (hash_region x0)) (hash_ty x1))
        (hash_ref_kind x2)
  | TRawPtr (x0, x1) ->
      HashBasic.combine (HashBasic.combine 5 (hash_ty x0)) (hash_ref_kind x1)
  | TFnDef x0 -> HashBasic.combine 6 ((hash_region_binder hash_fn_ptr) x0)
  | TFnPtr x0 -> HashBasic.combine 7 ((hash_region_binder hash_fun_sig) x0)
  | TDynTrait x0 -> HashBasic.combine 8 (hash_dyn_predicate x0)
  | TPattern (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 9 (hash_ty x0))
        (hash_type_pattern x1)
  | TNever -> 10
  | TVar x0 -> HashBasic.combine 11 ((hash_de_bruijn_var hash_type_var_id) x0)
  | TTraitType (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 12 (hash_trait_ref x0))
           (hash_assoc_type_id x1))
        (hash_generic_args x2)
  | TPtrMetadata x0 -> HashBasic.combine 13 (hash_ty x0)
  | TError x0 -> HashBasic.combine 14 (HashBasic.hash_string x0)

and hash_type_decl_ref : type_decl_ref -> int =
 fun (x : type_decl_ref) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_type_decl_id x.id))
       (hash_generic_args x.generics))
    ((HashBasic.hash_option hash_builtin_adt) x.builtin)

and hash_type_param : type_param -> int =
 fun (x : type_param) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_type_var_id x.index))
       (HashBasic.hash_string x.name))
    (hash_variance x.variance)

and hash_type_pattern : type_pattern -> int =
 fun (x : type_pattern) ->
  match x with
  | Range (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 0 (hash_constant_expr x0))
        (hash_constant_expr x1)
  | OrPattern x0 ->
      HashBasic.combine 1 ((HashBasic.hash_list hash_type_pattern) x0)
  | NotNull -> 2

and hash_unsizing_metadata : unsizing_metadata -> int =
 fun (x : unsizing_metadata) ->
  match x with
  | MetaLength x0 -> HashBasic.combine 0 (hash_constant_expr x0)
  | MetaVTable (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 1 (hash_trait_ref x0))
        (hash_constant_expr x1)
  | MetaVTableUpcast x0 ->
      HashBasic.combine 2 ((HashBasic.hash_list hash_field_id) x0)
  | MetaUnknown -> 3

and hash_variance : variance -> int =
 fun (x : variance) ->
  match x with
  | Covariant -> 0
  | Invariant -> 1
  | Contravariant -> 2
  | Bivariant -> 3
  | VaUnknown -> 4

and hash_variant_id : variant_id -> int =
 fun (x : variant_id) -> VariantId.hash_id x

(** Describes modifiers to the alignment and packing of the corresponding type.
    Represents [repr(align(n))] and [repr(packed(n))]. *)
type alignment_modifier = Align of int | Pack of int

(** Used for builtin items, rather than hardcoding these as strings. *)
and builtin_path_elem =
  | PeTuple of int  (** The tuple of the given arity. *)
  | PeStr
      (** [str], which is a struct containing a [[u8]] the standard library
          expects to be valid UTF-8. *)
  | PeClosure  (** A closure. *)
  | PeUse  (** A [use] declaration. *)
  | PeAnonConst  (** An anonymous constant. *)
  | PePromotedConst  (** A constant that rustc promoted out of a body. *)
  | PeClosureAsFn
      (** The function item we generate for a closure that is cast to a function
          pointer. *)
  | PeDropGlue
      (** The method we add to the [Destruct] trait to hold the drop glue. *)
  | PeVTable
      (** The vtable struct of a trait, or the vtable global of a trait impl. *)
  | PeVTableMethod  (** The version of a method that is stored in a vtable. *)
  | PeVTableDropShim  (** The [drop_in_place] shim stored in a vtable. *)

(** Additional information for closures. *)
and closure_info = {
  kind : closure_kind;
  closure_body : fun_decl_ref;
      (** The [FnFoo::call] method that contains the closure body. *)
  fn_once_impl : trait_impl_ref region_binder;
      (** The [FnOnce] implementation of this closure -- always exists. *)
  fn_mut_impl : trait_impl_ref region_binder option;
      (** The [FnMut] implementation of this closure, if any. *)
  fn_impl : trait_impl_ref region_binder option;
      (** The [Fn] implementation of this closure, if any. *)
  signature : fun_sig region_binder;
      (** The signature of the function that this closure represents. *)
}

and closure_kind = Fn | FnMut | FnOnce
and disambiguator = (Disambiguator.id[@visitors.opaque])

(** Decision tree used to determine the active variant by reading memory.
    Mirrors MiniRust's [Discriminator]. *)
and discriminator =
  | Known of variant_id  (** The variant is known. *)
  | Invalid  (** No valid variant (e.g., invalid tag value). *)
  | Branch of
      offset_expr
      * integer_type
      * (integer_value range_inclusive * discriminator) list
      * discriminator
      (** Branch on an integer value read from memory at [offset].

          Fields:
          - [offset]: Byte offset to read from.
          - [int_ty]: Integer type to read.
          - [children]: If the integer is in one of these ranges, continue with
            the given [Discriminator]. The ranges are sorted.
          - [fallback]: Fallback if no range in [children] matches. *)

and field = {
  span : span;
  attr_info : attr_info;
  field_name : string;
  is_positional : bool;
      (** Whether this field is positional, as in a tuple struct, tuple variant,
          or closure. If so, its name is based on its position, such as [_0];
          otherwise, it is a user-provided name. *)
  field_ty : ty;
}

(** The predecessor of a field in a struct or enum variant. *)
and field_predecessor = PredecessorField of field_id | PredecessorTag

(** There are two kinds of [impl] blocks:
    {ul
     {- impl blocks linked to a type ("inherent" impl blocks following Rust
        terminology):
        {@rust[
          impl<T> List<T> { ...}
        ]}
     }
     {- trait impl blocks:
        {@rust[
          impl<T> PartialEq for List<T> { ...}
        ]}
        We distinguish the two.
     }
    } *)
and impl_elem = ImplElemTy of ty binder | ImplElemTrait of trait_impl_id

(** Which marker traits this type implements. *)
and implements_marker_traits = {
  is_sized : bool;
  is_send : bool;
  is_sync : bool;
  is_freeze : bool;
  is_unpin : bool;
}

(** Represents whether a type or variant is inhabited. Like rustc's
    [InhabitedPredicate], this can depend on generic parameters and constant
    values. *)
and inhabited_predicate = inhabited_predicate_kind hash_consed

and inhabited_predicate_kind =
  | InhabitedPredicateTrue
  | InhabitedPredicateFalse
  | InhabitedPredicateConstIsZero of constant_expr
      (** Inhabited when this constant is zero. *)
  | InhabitedPredicateGenericType of ty
      (** Inhabited when this generic type is inhabited. *)
  | InhabitedPredicateAnd of inhabited_predicate list
  | InhabitedPredicateOr of inhabited_predicate list

(** Meta information about an item (function, trait decl, trait impl, type decl,
    global). *)
and item_meta = {
  name : name;
  span : span;
  source_text : string option;
      (** The source code that corresponds to this item. *)
  attr_info : attr_info;  (** Attributes and visibility. *)
  is_local : bool;
      (** [true] if the type decl is a local type decl, [false] if it comes from
          an external crate. *)
  started_from : bool;
      (** Whether this item was selected as a starting point for translation
          (using [--start-from], or by default all the top-level items in the
          main crate). *)
  is_extern : bool;
      (** Whether this item is declared in an [extern { .. }] block. *)
  opacity : item_opacity;
      (** Whether this item is considered opaque. For function and globals, this
          means we don't translate the body (the code); for ADTs, this means we
          don't translate the fields/variants. For traits and trait impls, this
          doesn't change anything. For modules, this means we don't explore its
          contents (we still translate any of its items mentioned from somewhere
          else).

          This can happen either if the item was annotated with
          [#[charon::opaque]] or if it was declared opaque via a command-line
          argument. *)
  lang_item : rustc_lang_item option;
      (** If the item is a rustc lang item, record which one it is. *)
  diagnostic_item : string option;
      (** If the item is a rustc diagnostic item, record its internal
          identifier. *)
  has_errors : bool;
      (** Whether an error occurred while translating this item. *)
}

(** How much to translate for a given item. *)
and item_opacity =
  | Transparent  (** Translate the item fully. *)
  | Foreign
      (** Translate the item depending on the normal rust visibility of its
          contents: for types, we translate fully if it is a struct with public
          fields or an enum; for other items this is equivalent to [Opaque]. *)
  | ItemOpaque
      (** Translate the item name and signature, but not its contents. For
          function and globals, this means we don't translate the body (the
          code); for ADTs, this means we don't translate the fields/variants.
          For traits and trait impls, this doesn't change anything. For modules,
          this means we don't explore its contents (we still translate any of
          its items mentioned from somewhere else).

          This can happen either if the item was annotated with
          [#[charon::opaque]] or if it was declared opaque via a command-line
          argument. *)
  | Invisible
      (** Translate nothing of this item. The corresponding map will not have an
          entry for the [ItemId]. Useful when even the signature of the item
          causes errors. *)

(** A representation of all the valid lang items in Rust. *)
and rustc_lang_item =
  | RustcLangItemSized  (**The [sized] lang item. *)
  | RustcLangItemMetaSized  (**The [meta_sized] lang item. *)
  | RustcLangItemPointeeSized  (**The [pointee_sized] lang item. *)
  | RustcLangItemUnsize  (**The [unsize] lang item. *)
  | RustcLangItemAlignOf  (**The [mem_align_const] lang item. *)
  | RustcLangItemSizeOf  (**The [mem_size_const] lang item. *)
  | RustcLangItemOffsetOf  (**The [offset_of] lang item. *)
  | RustcLangItemStructuralPeq
      (** The [structural_peq] lang item. Trait injected by
          [#[derive(PartialEq)]], (i.e. "Partial EQ"). *)
  | RustcLangItemCopy  (**The [copy] lang item. *)
  | RustcLangItemClone  (**The [clone] lang item. *)
  | RustcLangItemCloneFn  (**The [clone_fn] lang item. *)
  | RustcLangItemUseCloned  (**The [use_cloned] lang item. *)
  | RustcLangItemTrivialClone  (**The [trivial_clone] lang item. *)
  | RustcLangItemSync  (**The [sync] lang item. *)
  | RustcLangItemDiscriminantKind  (**The [discriminant_kind] lang item. *)
  | RustcLangItemDiscriminant
      (** The [discriminant_type] lang item. The associated item of the
          [DiscriminantKind] trait. *)
  | RustcLangItemPointeeTrait  (**The [pointee_trait] lang item. *)
  | RustcLangItemMetadata  (**The [metadata_type] lang item. *)
  | RustcLangItemDynMetadata  (**The [dyn_metadata] lang item. *)
  | RustcLangItemNonNull  (**The [non_null] lang item. *)
  | RustcLangItemFreeze  (**The [freeze] lang item. *)
  | RustcLangItemUnsafeUnpin  (**The [unsafe_unpin] lang item. *)
  | RustcLangItemFnPtrTrait  (**The [fn_ptr_trait] lang item. *)
  | RustcLangItemFnPtrAsPtr  (**The [fn_ptr_as_ptr] lang item. *)
  | RustcLangItemFnPtrFromPtr  (**The [fn_ptr_from_ptr] lang item. *)
  | RustcLangItemCode  (**The [code] lang item. *)
  | RustcLangItemDrop  (**The [drop] lang item. *)
  | RustcLangItemDestruct  (**The [destruct] lang item. *)
  | RustcLangItemAsyncDrop  (**The [async_drop] lang item. *)
  | RustcLangItemAsyncDropInPlace  (**The [async_drop_in_place] lang item. *)
  | RustcLangItemCoerceUnsized  (**The [coerce_unsized] lang item. *)
  | RustcLangItemDispatchFromDyn  (**The [dispatch_from_dyn] lang item. *)
  | RustcLangItemTryAsDyn  (**The [try_as_dyn] lang item. *)
  | RustcLangItemTransmuteOpts  (**The [transmute_opts] lang item. *)
  | RustcLangItemTransmuteTrait  (**The [transmute_trait] lang item. *)
  | RustcLangItemAdd  (**The [add] lang item. *)
  | RustcLangItemSub  (**The [sub] lang item. *)
  | RustcLangItemMul  (**The [mul] lang item. *)
  | RustcLangItemDiv  (**The [div] lang item. *)
  | RustcLangItemRem  (**The [rem] lang item. *)
  | RustcLangItemNeg  (**The [neg] lang item. *)
  | RustcLangItemNot  (**The [not] lang item. *)
  | RustcLangItemBitXor  (**The [bitxor] lang item. *)
  | RustcLangItemBitAnd  (**The [bitand] lang item. *)
  | RustcLangItemBitOr  (**The [bitor] lang item. *)
  | RustcLangItemShl  (**The [shl] lang item. *)
  | RustcLangItemShr  (**The [shr] lang item. *)
  | RustcLangItemAddAssign  (**The [add_assign] lang item. *)
  | RustcLangItemSubAssign  (**The [sub_assign] lang item. *)
  | RustcLangItemMulAssign  (**The [mul_assign] lang item. *)
  | RustcLangItemDivAssign  (**The [div_assign] lang item. *)
  | RustcLangItemRemAssign  (**The [rem_assign] lang item. *)
  | RustcLangItemBitXorAssign  (**The [bitxor_assign] lang item. *)
  | RustcLangItemBitAndAssign  (**The [bitand_assign] lang item. *)
  | RustcLangItemBitOrAssign  (**The [bitor_assign] lang item. *)
  | RustcLangItemShlAssign  (**The [shl_assign] lang item. *)
  | RustcLangItemShrAssign  (**The [shr_assign] lang item. *)
  | RustcLangItemIndex  (**The [index] lang item. *)
  | RustcLangItemIndexMut  (**The [index_mut] lang item. *)
  | RustcLangItemUnsafeCell  (**The [unsafe_cell] lang item. *)
  | RustcLangItemCovariantUnsafeCell
      (**The [covariant_unsafe_cell] lang item. *)
  | RustcLangItemUnsafePinned  (**The [unsafe_pinned] lang item. *)
  | RustcLangItemVaArgSafe  (**The [va_arg_safe] lang item. *)
  | RustcLangItemVaList  (**The [va_list] lang item. *)
  | RustcLangItemComplex  (**The [complex] lang item. *)
  | RustcLangItemDeref  (**The [deref] lang item. *)
  | RustcLangItemDerefMut  (**The [deref_mut] lang item. *)
  | RustcLangItemDerefPure  (**The [deref_pure] lang item. *)
  | RustcLangItemDerefTarget  (**The [deref_target] lang item. *)
  | RustcLangItemReceiver  (**The [receiver] lang item. *)
  | RustcLangItemReceiverTarget  (**The [receiver_target] lang item. *)
  | RustcLangItemLegacyReceiver  (**The [legacy_receiver] lang item. *)
  | RustcLangItemFn  (**The [Fn] lang item. *)
  | RustcLangItemFnMut  (**The [fn_mut] lang item. *)
  | RustcLangItemFnOnce  (**The [fn_once] lang item. *)
  | RustcLangItemFnStatic  (**The [fn_static] lang item. *)
  | RustcLangItemAsyncFn  (**The [async_fn] lang item. *)
  | RustcLangItemAsyncFnMut  (**The [async_fn_mut] lang item. *)
  | RustcLangItemAsyncFnOnce  (**The [async_fn_once] lang item. *)
  | RustcLangItemAsyncFnOnceOutput  (**The [async_fn_once_output] lang item. *)
  | RustcLangItemCallOnceFuture  (**The [call_once_future] lang item. *)
  | RustcLangItemCallRefFuture  (**The [call_ref_future] lang item. *)
  | RustcLangItemAsyncFnKindHelper  (**The [async_fn_kind_helper] lang item. *)
  | RustcLangItemAsyncFnKindUpvars  (**The [async_fn_kind_upvars] lang item. *)
  | RustcLangItemFnOnceOutput  (**The [fn_once_output] lang item. *)
  | RustcLangItemIterator  (**The [iterator] lang item. *)
  | RustcLangItemFusedIterator  (**The [fused_iterator] lang item. *)
  | RustcLangItemFuture  (**The [future_trait] lang item. *)
  | RustcLangItemFutureOutput  (**The [future_output] lang item. *)
  | RustcLangItemAsyncIterator  (**The [async_iterator] lang item. *)
  | RustcLangItemCoroutineState  (**The [coroutine_state] lang item. *)
  | RustcLangItemCoroutine  (**The [coroutine] lang item. *)
  | RustcLangItemCoroutineReturn  (**The [coroutine_return] lang item. *)
  | RustcLangItemCoroutineYield  (**The [coroutine_yield] lang item. *)
  | RustcLangItemCoroutineResume  (**The [coroutine_resume] lang item. *)
  | RustcLangItemUnpin  (**The [unpin] lang item. *)
  | RustcLangItemPin  (**The [Pin] lang item. *)
  | RustcLangItemOrderingEnum  (**The [Ordering] lang item. *)
  | RustcLangItemPartialEq  (**The [eq] lang item. *)
  | RustcLangItemPartialOrd  (**The [partial_ord] lang item. *)
  | RustcLangItemCVoid  (**The [c_void] lang item. *)
  | RustcLangItemType  (**The [type_info] lang item. *)
  | RustcLangItemTypeGeneric  (**The [type_info_generic] lang item. *)
  | RustcLangItemTypeId  (**The [type_id] lang item. *)
  | RustcLangItemPanic  (**The [panic] lang item. *)
  | RustcLangItemPanicNounwind  (**The [panic_nounwind] lang item. *)
  | RustcLangItemPanicFmt  (**The [panic_fmt] lang item. *)
  | RustcLangItemPanicDisplay  (**The [panic_display] lang item. *)
  | RustcLangItemConstPanicFmt  (**The [const_panic_fmt] lang item. *)
  | RustcLangItemPanicBoundsCheck  (**The [panic_bounds_check] lang item. *)
  | RustcLangItemPanicMisalignedPointerDereference
      (**The [panic_misaligned_pointer_dereference] lang item. *)
  | RustcLangItemPanicInfo  (**The [panic_info] lang item. *)
  | RustcLangItemPanicLocation  (**The [panic_location] lang item. *)
  | RustcLangItemPanicImpl  (**The [panic_impl] lang item. *)
  | RustcLangItemPanicCannotUnwind  (**The [panic_cannot_unwind] lang item. *)
  | RustcLangItemPanicInCleanup  (**The [panic_in_cleanup] lang item. *)
  | RustcLangItemPanicAddOverflow
      (** The [panic_const_add_overflow] lang item. Constant panic messages,
          used for codegen of MIR asserts. *)
  | RustcLangItemPanicSubOverflow
      (**The [panic_const_sub_overflow] lang item. *)
  | RustcLangItemPanicMulOverflow
      (**The [panic_const_mul_overflow] lang item. *)
  | RustcLangItemPanicDivOverflow
      (**The [panic_const_div_overflow] lang item. *)
  | RustcLangItemPanicRemOverflow
      (**The [panic_const_rem_overflow] lang item. *)
  | RustcLangItemPanicNegOverflow
      (**The [panic_const_neg_overflow] lang item. *)
  | RustcLangItemPanicShrOverflow
      (**The [panic_const_shr_overflow] lang item. *)
  | RustcLangItemPanicShlOverflow
      (**The [panic_const_shl_overflow] lang item. *)
  | RustcLangItemPanicDivZero  (**The [panic_const_div_by_zero] lang item. *)
  | RustcLangItemPanicRemZero  (**The [panic_const_rem_by_zero] lang item. *)
  | RustcLangItemPanicCoroutineResumed
      (**The [panic_const_coroutine_resumed] lang item. *)
  | RustcLangItemPanicAsyncFnResumed
      (**The [panic_const_async_fn_resumed] lang item. *)
  | RustcLangItemPanicAsyncGenFnResumed
      (**The [panic_const_async_gen_fn_resumed] lang item. *)
  | RustcLangItemPanicGenFnNone  (**The [panic_const_gen_fn_none] lang item. *)
  | RustcLangItemPanicCoroutineResumedPanic
      (**The [panic_const_coroutine_resumed_panic] lang item. *)
  | RustcLangItemPanicAsyncFnResumedPanic
      (**The [panic_const_async_fn_resumed_panic] lang item. *)
  | RustcLangItemPanicAsyncGenFnResumedPanic
      (**The [panic_const_async_gen_fn_resumed_panic] lang item. *)
  | RustcLangItemPanicGenFnNonePanic
      (**The [panic_const_gen_fn_none_panic] lang item. *)
  | RustcLangItemPanicNullPointerDereference
      (**The [panic_null_pointer_dereference] lang item. *)
  | RustcLangItemPanicNullReferenceConstructed
      (**The [panic_null_reference_constructed] lang item. *)
  | RustcLangItemPanicInvalidEnumConstruction
      (**The [panic_invalid_enum_construction] lang item. *)
  | RustcLangItemPanicCoroutineResumedDrop
      (**The [panic_const_coroutine_resumed_drop] lang item. *)
  | RustcLangItemPanicAsyncFnResumedDrop
      (**The [panic_const_async_fn_resumed_drop] lang item. *)
  | RustcLangItemPanicAsyncGenFnResumedDrop
      (**The [panic_const_async_gen_fn_resumed_drop] lang item. *)
  | RustcLangItemPanicGenFnNoneDrop
      (**The [panic_const_gen_fn_none_drop] lang item. *)
  | RustcLangItemBeginPanic
      (** The [begin_panic] lang item. libstd panic entry point. Necessary for
          const eval to be able to catch it *)
  | RustcLangItemFormatArgument  (**The [format_argument] lang item. *)
  | RustcLangItemFormatArguments  (**The [format_arguments] lang item. *)
  | RustcLangItemDropGlue  (**The [drop_glue] lang item. *)
  | RustcLangItemAllocLayout  (**The [alloc_layout] lang item. *)
  | RustcLangItemStart
      (** The [start] lang item. For all binary crates without [#![no_main]],
          Rust will generate a "main" function. The exact name and signature are
          target-dependent. The "main" function will invoke this lang item,
          passing it the [argc] and [argv] (or null, if those don't exist on the
          current target) as well as the user-defined [fn main] from the binary
          crate. *)
  | RustcLangItemEhPersonality  (**The [eh_personality] lang item. *)
  | RustcLangItemCompilerMove  (**The [compiler_move] lang item. *)
  | RustcLangItemCompilerCopy  (**The [compiler_copy] lang item. *)
  | RustcLangItemOwnedBox  (**The [owned_box] lang item. *)
  | RustcLangItemGlobalAlloc  (**The [global_alloc_ty] lang item. *)
  | RustcLangItemPhantomData  (**The [phantom_data] lang item. *)
  | RustcLangItemManuallyDrop  (**The [manually_drop] lang item. *)
  | RustcLangItemMaybeDangling  (**The [maybe_dangling] lang item. *)
  | RustcLangItemBikeshedGuaranteedNoDrop
      (**The [bikeshed_guaranteed_no_drop] lang item. *)
  | RustcLangItemMaybeUninit  (**The [maybe_uninit] lang item. *)
  | RustcLangItemTermination  (**The [termination] lang item. *)
  | RustcLangItemTry  (**The [Try] lang item. *)
  | RustcLangItemTuple  (**The [tuple_trait] lang item. *)
  | RustcLangItemSliceLen  (**The [slice_len_fn] lang item. *)
  | RustcLangItemTryTraitFromResidual  (**The [from_residual] lang item. *)
  | RustcLangItemTryTraitFromOutput  (**The [from_output] lang item. *)
  | RustcLangItemTryTraitBranch  (**The [branch] lang item. *)
  | RustcLangItemTryTraitFromYeet  (**The [from_yeet] lang item. *)
  | RustcLangItemResidualIntoTryType  (**The [into_try_type] lang item. *)
  | RustcLangItemCoercePointeeValidated
      (**The [coerce_pointee_validated] lang item. *)
  | RustcLangItemConstParamTy  (**The [const_param_ty] lang item. *)
  | RustcLangItemPoll  (**The [Poll] lang item. *)
  | RustcLangItemPollReady  (**The [Ready] lang item. *)
  | RustcLangItemPollPending  (**The [Pending] lang item. *)
  | RustcLangItemAsyncGenReady  (**The [AsyncGenReady] lang item. *)
  | RustcLangItemAsyncGenPending  (**The [AsyncGenPending] lang item. *)
  | RustcLangItemAsyncGenFinished  (**The [AsyncGenFinished] lang item. *)
  | RustcLangItemResumeTy  (**The [ResumeTy] lang item. *)
  | RustcLangItemGetContext  (**The [get_context] lang item. *)
  | RustcLangItemContext  (**The [Context] lang item. *)
  | RustcLangItemFuturePoll  (**The [poll] lang item. *)
  | RustcLangItemAsyncIteratorPollNext
      (**The [async_iterator_poll_next] lang item. *)
  | RustcLangItemIntoAsyncIterIntoIter
      (**The [into_async_iter_into_iter] lang item. *)
  | RustcLangItemOption  (**The [Option] lang item. *)
  | RustcLangItemOptionSome  (**The [Some] lang item. *)
  | RustcLangItemOptionNone  (**The [None] lang item. *)
  | RustcLangItemResultOk  (**The [Ok] lang item. *)
  | RustcLangItemResultErr  (**The [Err] lang item. *)
  | RustcLangItemControlFlowContinue  (**The [Continue] lang item. *)
  | RustcLangItemControlFlowBreak  (**The [Break] lang item. *)
  | RustcLangItemIntoFutureIntoFuture  (**The [into_future] lang item. *)
  | RustcLangItemIntoIterIntoIter  (**The [into_iter] lang item. *)
  | RustcLangItemIteratorNext  (**The [next] lang item. *)
  | RustcLangItemPinNewUnchecked  (**The [new_unchecked] lang item. *)
  | RustcLangItemRangeFrom  (**The [RangeFrom] lang item. *)
  | RustcLangItemRangeFull  (**The [RangeFull] lang item. *)
  | RustcLangItemRangeInclusiveStruct  (**The [RangeInclusive] lang item. *)
  | RustcLangItemRangeInclusiveNew  (**The [range_inclusive_new] lang item. *)
  | RustcLangItemRange  (**The [Range] lang item. *)
  | RustcLangItemRangeToInclusive  (**The [RangeToInclusive] lang item. *)
  | RustcLangItemRangeTo  (**The [RangeTo] lang item. *)
  | RustcLangItemRangeMax  (**The [RangeMax] lang item. *)
  | RustcLangItemRangeMin  (**The [RangeMin] lang item. *)
  | RustcLangItemRangeSub  (**The [RangeSub] lang item. *)
  | RustcLangItemRangeFromCopy  (**The [RangeFromCopy] lang item. *)
  | RustcLangItemRangeCopy  (**The [RangeCopy] lang item. *)
  | RustcLangItemRangeInclusiveCopy  (**The [RangeInclusiveCopy] lang item. *)
  | RustcLangItemRangeToInclusiveCopy
      (**The [RangeToInclusiveCopy] lang item. *)
  | RustcLangItemString  (**The [String] lang item. *)
  | RustcLangItemCStr  (**The [CStr] lang item. *)
  | RustcLangItemContractBuildCheckEnsures
      (**The [contract_build_check_ensures] lang item. *)
  | RustcLangItemContractCheckRequires
      (**The [contract_check_requires] lang item. *)
  | RustcLangItemDefaultTrait4  (**The [default_trait4] lang item. *)
  | RustcLangItemDefaultTrait3  (**The [default_trait3] lang item. *)
  | RustcLangItemDefaultTrait2  (**The [default_trait2] lang item. *)
  | RustcLangItemDefaultTrait1  (**The [default_trait1] lang item. *)
  | RustcLangItemContractCheckEnsures
      (**The [contract_check_ensures] lang item. *)
  | RustcLangItemReborrow  (**The [reborrow] lang item. *)
  | RustcLangItemCoerceShared  (**The [coerce_shared] lang item. *)
  | RustcLangItemFieldRepresentingType
      (**The [field_representing_type] lang item. *)
  | RustcLangItemField  (**The [field] lang item. *)
  | RustcLangItemFieldBase  (**The [field_base] lang item. *)
  | RustcLangItemFieldType  (**The [field_type] lang item. *)
  | RustcLangItemFieldOffset  (**The [field_offset] lang item. *)
  | RustcLangItemFrom  (**The [From] lang item. *)
  | RustcLangItemFromFn  (**The [from] lang item. *)
  | RustcLangItemFnPtr  (**The [FnPtr] lang item. *)

(** Type layout information.

    Does not include information about niches. If the type does not have a fully
    known layout (e.g. it is ?Sized) some of the layout parts are not available.
*)
and layout = {
  size : size;  (** The size of the type in bytes. *)
  align : size;  (** The alignment, in bytes. *)
  discriminator : discriminator option;
      (** Decision tree that determines the active variant by reading memory.
          Only [Some] for enums. *)
  inhabited : inhabited_predicate;
      (** Whether the type has any valid value. Note that uninhabited types can
          have arbitrary layouts: [(u32, !)] has space for the [u32] and
          [enum E2 { A, B(!), C(i32, !) }] may have space for a discriminant. *)
  variant_layouts : variant_layout option list;
      (** Map from [VariantId] to the corresponding field layouts. Some variants
          don't have a meaningful layout due to being uninhabited (though an
          uninhabited variant may have a layout). Structs and unions are modeled
          as having exactly one variant. *)
  repr : repr_options;
      (** The representation options of this type declaration as annotated by
          the user. *)
}

(** Layout information given by the metadata of an unsized type. *)
and metadata_value =
  | DynSize
      (** For a DST with [dyn Trait] metadata, this refers to the size found in
          the metadata. *)
  | DynAlign
      (** For a DST with [dyn Trait] metadata, this refers to the alignment
          found in the metadata. *)
  | SliceLength
      (** For a DST with slice metadata, this refers to the length found in the
          metadata. *)

(** An item name/path

    A name really is a list of strings. However, we sometimes need to introduce
    unique indices to disambiguate. This mostly happens because of "impl"
    blocks:
    {@rust[
      impl<T> List<T> {
        ...
      }
    ]}

    A type in Rust can have several "impl" blocks, and those blocks can contain
    items with similar names. For this reason, we need to disambiguate them with
    unique indices. Rustc calls those "disambiguators". In rustc, this gives
    names like this:
    - [betree_main::betree::NodeIdCounter{impl#0}::new]
    - note that impl blocks can be nested, and macros sometimes generate weird
      names (which require disambiguation):
      [betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}]

    Finally, the paths used by rustc are a lot more precise and explicit than
    those we expose in LLBC: for instance, every identifier belongs to a
    specific namespace (value namespace, type namespace, etc.), and is coupled
    with a disambiguator.

    On our side, we want to stay high-level and simple: we use string
    identifiers as much as possible, insert disambiguators only when necessary
    (for instance when we find an "impl" block or when two loaded crates have
    the same name) and check that the disambiguator is useless in the other
    situations (i.e., the disambiguator is always equal to 0).

    Moreover, the items are uniquely disambiguated by their (integer) ids
    ([TypeDeclId], etc.), and when extracting the code we have to deal with name
    clashes anyway. Still, we might want to be more precise in the future.

    Also note that the first path element in the name is always the crate name.
*)
and name = (path_elem list[@visitors.opaque])

(** An expression denoting an offset in bytes. *)
and offset_expr = {
  guarantee : offset_guarantee option;
      (** The guarantees about this offset that can be relied on according to
          the Rust Reference. *)
  chosen : int option;
      (** The offset chosen by this rustc run. [None] for unsized fields. *)
}

(** Guaranteed facts about a field offset. *)
and offset_guarantee =
  | AtOffset of size_expr  (** Guaranteed to be exactly at the given offset. *)
  | GuaranteedAlignment of size_expr
      (** Guaranteed only to be aligned to the given expression. *)
  | ReprCField of field_predecessor
      (** This offset is computed by the layout algorithm for C: take the
          previous field offset, add the previous field size, and align to the
          current field alignment (as capped by [packed]). *)

(** See the comments for [Name] *)
and path_elem =
  | PeIdent of string * disambiguator
  | PeImpl of impl_elem
  | PeInstantiated of generic_args binder
      (** This item was obtained by instantiating its parent with the given
          args. The binder binds the parameters of the new items. If the binder
          binds nothing then this is a monomorphization. *)
  | PeTarget of string
      (** This item is only available on the given target. Only appears in
          multi-target mode. *)
  | PeBuiltin of builtin_path_elem * disambiguator
      (** A path element that doesn't come from the source code: either a
          builtin type such as tuples, or an item that has no name of its own
          such as a closure or a vtable. *)

(** The metadata stored in a pointer. That's the information stored in pointers
    alongside their address. It's empty for [Sized] types, and interesting for
    unsized aka dynamically-sized types. *)
and ptr_metadata =
  | NoMetadata  (** Types that need no metadata, namely [T: Sized] types. *)
  | Length
      (** Metadata for [[T]] and [str], and user-defined types that directly or
          indirectly contain one of the two. Of type [usize]. Notably, length
          for [[T]] denotes the number of elements in the slice. While for [str]
          it denotes the number of bytes in the string. *)
  | VTable of type_decl_ref
      (** Metadata for [dyn Trait], referring to the vtable struct. Has type
          [&'static vtable] *)
  | InheritFrom of ty
      (** Unknown due to generics, but will inherit from the given type. This is
          consistent with [<Ty as Pointee>::Metadata]. Of type
          [TyKind::Metadata(Ty)]. *)

(** Describes which layout algorithm is used for representing the corresponding
    type. Depends on the [#[repr(...)]] used. *)
and repr_algorithm =
  | Rust
      (** The default layout algorithm. Used without an explicit [ŗepr] or for
          [repr(Rust)]. *)
  | C  (** The C layout algorithm as enforced by [repr(C)]. *)

(** The representation options as annotated by the user.

    NOTE: This does not include less common/unstable representations such as
    [#[repr(simd)]] or the compiler internal [#[repr(linear)]]. Similarly, enum
    discriminant representations are encoded in [[Variant::discriminant]] and
    [[Discriminator]] instead. *)
and repr_options = {
  repr_algo : repr_algorithm;
  align_modif : alignment_modifier option;
  transparent : bool;
  explicit_discr_type : integer_type option;
      (** The type supplied to [repr(..)], if any. *)
}

(** An expression denoting a size in bytes. *)
and size = {
  chosen : size_expr option;
      (** The size chosen by this rustc run. For sized types, this is a plain
          integer, and for unsized types, this is an expression describing how
          to compute this size based on the values found in the pointer
          metadata. This can be [None] for polymorphic types. *)
  guarantee : size_expr option;
      (** The guarantees about this size that can be relied on according to the
          Rust Reference. *)
}

(** An expression that represents a size in bytes. *)
and size_expr = size_expr_kind hash_consed

and size_expr_kind =
  | SizeExprConstant of constant_expr
      (** An arbitrary constant of type [usize]. *)
  | SizeExprFromMetadata of metadata_value
      (** Layout information stored in the pointer metadata to this object. *)
  | SizeExprMax of size_expr list
  | SizeExprMin of size_expr list
  | SizeExprPlus of size_expr * size_expr
  | SizeExprScale of size_expr * constant_expr  (** Multiply by a constant. *)
  | SizeExprAtLeast of size_expr
      (** The size is at least the value of this expression. *)
  | SizeExprAlignTo of size_expr * size_expr
      (** The next multiple of [target_align] from [base].

          Fields:
          - [base]
          - [target_align] *)
  | SizeExprIfInhabited of ty * size_expr * size_expr
      (** A size expression that depens on whether the given type is inhabited.

          Fields:
          - [ty]
          - [then_size]
          - [else_size] *)

(** A type declaration.

    Types can be opaque or transparent.

    Transparent types are local types not marked as opaque. Opaque types are the
    others: local types marked as opaque, and non-local types (coming from
    external dependencies).

    In case the type is transparent, the declaration also contains the type
    definition (see [TypeDeclKind]).

    A type can only be an ADT (structure or enumeration), as type aliases are
    inlined in MIR. *)
and type_decl = {
  def_id : type_decl_id;
  item_meta : item_meta;  (** Meta information associated with the item. *)
  generics : generic_params;
  src : type_source;
      (** The context of the type: distinguishes top-level items from
          closure-related items etc. *)
  kind : type_decl_kind;  (** The type kind: enum, struct, or opaque. *)
  layout : (string * layout) list;
      (** The layout of the type for each target. Information may be partial
          because of generics or dynamically-sized types. If we cannot compute a
          layout, the target has no entry. *)
  ptr_metadata : ptr_metadata;
      (** The metadata associated with a pointer to the type. *)
  marker_traits : implements_marker_traits option;
      (** Which built-in marker traits are implemented by this type. This is
          only known for monomorphic types. *)
}

and type_decl_kind =
  | Struct of field list
  | Enum of variant list
  | Union of field list
  | Opaque
      (** An opaque type.

          Either a local type marked as opaque, or an external type. *)
  | Alias of ty
      (** An alias to another type. This only shows up in the top-level list of
          items, as rustc inlines uses of type aliases everywhere else. *)
  | TDeclError of string
      (** Used if an error happened during the extraction, and we don't panic on
          error. *)

(** Where a given type came from. *)
and type_source =
  | NormalType  (** A normal type declaration. *)
  | ClosureType of closure_info
      (** The struct that carries the captured variables of a closure.

          Fields:
          - [info] *)
  | VTableType of dyn_predicate * v_table_field list * field_id option list
      (** Defines the vtable struct for a trait.

          Fields:
          - [dyn_predicate]: The [dyn Trait] predicate implemented by this
            vtable.
          - [field_map]: Record what each vtable field means.
          - [supertrait_map]: For each implied clause that is also a supertrait
            clause, records which field of the vtable corresponds to it. *)
  | BuiltinType of builtin_adt
      (** A type declaration synthesised for a builtin ADT. *)

and v_table_field =
  | VTableSize
  | VTableAlign
  | VTableDrop
  | VTableMethod of trait_method_id
  | VTableSuperTrait of trait_clause_id

and variant = {
  id : variant_id;
  span : span;
  attr_info : attr_info;
  variant_name : string;
  fields : field list;
  discriminant : integer_value;
      (** The discriminant value outputted by [std::mem::discriminant] for this
          variant. This can be different than the value stored in memory (called
          [tag]); that one is described by [[Discriminator]] and
          [[VariantLayout::tagger]]. *)
}

(** Simplified layout of a single variant.

    Maps fields to their offset within the layout. *)
and variant_layout = {
  field_offsets : offset_expr list;  (** The offset of each field. *)
  inhabited : inhabited_predicate;
      (** Whether the variant has any valid possible value. Note that
          uninhabited types can have arbitrary layouts. *)
  tagger : (int * integer_value) list;
      (** How to write the tag when constructing this variant. Each entry means:
          write [value] at byte [offset]. Mirrors MiniRust's [Variant::tagger].
      *)
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
      ancestors = [ "iter_ty" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_type_decl";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_ty" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

let rec hash_alignment_modifier : alignment_modifier -> int =
 fun (x : alignment_modifier) ->
  match x with
  | Align x0 -> HashBasic.combine 0 (HashBasic.hash_int x0)
  | Pack x0 -> HashBasic.combine 1 (HashBasic.hash_int x0)

and hash_builtin_path_elem : builtin_path_elem -> int =
 fun (x : builtin_path_elem) ->
  match x with
  | PeTuple x0 -> HashBasic.combine 0 (HashBasic.hash_int x0)
  | PeStr -> 1
  | PeClosure -> 2
  | PeUse -> 3
  | PeAnonConst -> 4
  | PePromotedConst -> 5
  | PeClosureAsFn -> 6
  | PeDropGlue -> 7
  | PeVTable -> 8
  | PeVTableMethod -> 9
  | PeVTableDropShim -> 10

and hash_closure_info : closure_info -> int =
 fun (x : closure_info) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine
                (HashBasic.combine 0 (hash_closure_kind x.kind))
                (hash_fun_decl_ref x.closure_body))
             ((hash_region_binder hash_trait_impl_ref) x.fn_once_impl))
          ((HashBasic.hash_option (hash_region_binder hash_trait_impl_ref))
             x.fn_mut_impl))
       ((HashBasic.hash_option (hash_region_binder hash_trait_impl_ref))
          x.fn_impl))
    ((hash_region_binder hash_fun_sig) x.signature)

and hash_closure_kind : closure_kind -> int =
 fun (x : closure_kind) ->
  match x with
  | Fn -> 0
  | FnMut -> 1
  | FnOnce -> 2

and hash_disambiguator : disambiguator -> int =
 fun (x : disambiguator) -> Disambiguator.hash_id x

and hash_discriminator : discriminator -> int =
 fun (x : discriminator) ->
  match x with
  | Known x0 -> HashBasic.combine 0 (hash_variant_id x0)
  | Invalid -> 1
  | Branch (x0, x1, x2, x3) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine
              (HashBasic.combine 2 (hash_offset_expr x0))
              (hash_integer_type x1))
           ((HashBasic.hash_list (fun (x0, x1) ->
                 HashBasic.combine
                   (HashBasic.combine 0
                      ((hash_range_inclusive hash_integer_value) x0))
                   (hash_discriminator x1)))
              x2))
        (hash_discriminator x3)

and hash_field : field -> int =
 fun (x : field) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine 0 (hash_span x.span))
             (hash_attr_info x.attr_info))
          (HashBasic.hash_string x.field_name))
       (HashBasic.hash_bool x.is_positional))
    (hash_ty x.field_ty)

and hash_field_predecessor : field_predecessor -> int =
 fun (x : field_predecessor) ->
  match x with
  | PredecessorField x0 -> HashBasic.combine 0 (hash_field_id x0)
  | PredecessorTag -> 1

and hash_impl_elem : impl_elem -> int =
 fun (x : impl_elem) ->
  match x with
  | ImplElemTy x0 -> HashBasic.combine 0 ((hash_binder hash_ty) x0)
  | ImplElemTrait x0 -> HashBasic.combine 1 (hash_trait_impl_id x0)

and hash_implements_marker_traits : implements_marker_traits -> int =
 fun (x : implements_marker_traits) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine 0 (HashBasic.hash_bool x.is_sized))
             (HashBasic.hash_bool x.is_send))
          (HashBasic.hash_bool x.is_sync))
       (HashBasic.hash_bool x.is_freeze))
    (HashBasic.hash_bool x.is_unpin)

and hash_inhabited_predicate : inhabited_predicate -> int =
 fun (x : inhabited_predicate) ->
  (hash_hash_consed hash_inhabited_predicate_kind) x

and hash_inhabited_predicate_kind : inhabited_predicate_kind -> int =
 fun (x : inhabited_predicate_kind) ->
  match x with
  | InhabitedPredicateTrue -> 0
  | InhabitedPredicateFalse -> 1
  | InhabitedPredicateConstIsZero x0 ->
      HashBasic.combine 2 (hash_constant_expr x0)
  | InhabitedPredicateGenericType x0 -> HashBasic.combine 3 (hash_ty x0)
  | InhabitedPredicateAnd x0 ->
      HashBasic.combine 4 ((HashBasic.hash_list hash_inhabited_predicate) x0)
  | InhabitedPredicateOr x0 ->
      HashBasic.combine 5 ((HashBasic.hash_list hash_inhabited_predicate) x0)

and hash_item_meta : item_meta -> int =
 fun (x : item_meta) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine
                (HashBasic.combine
                   (HashBasic.combine
                      (HashBasic.combine
                         (HashBasic.combine
                            (HashBasic.combine
                               (HashBasic.combine 0 (hash_name x.name))
                               (hash_span x.span))
                            ((HashBasic.hash_option HashBasic.hash_string)
                               x.source_text))
                         (hash_attr_info x.attr_info))
                      (HashBasic.hash_bool x.is_local))
                   (HashBasic.hash_bool x.started_from))
                (HashBasic.hash_bool x.is_extern))
             (hash_item_opacity x.opacity))
          ((HashBasic.hash_option hash_rustc_lang_item) x.lang_item))
       ((HashBasic.hash_option HashBasic.hash_string) x.diagnostic_item))
    (HashBasic.hash_bool x.has_errors)

and hash_item_opacity : item_opacity -> int =
 fun (x : item_opacity) ->
  match x with
  | Transparent -> 0
  | Foreign -> 1
  | ItemOpaque -> 2
  | Invisible -> 3

and hash_rustc_lang_item : rustc_lang_item -> int =
 fun (x : rustc_lang_item) ->
  match x with
  | RustcLangItemSized -> 0
  | RustcLangItemMetaSized -> 1
  | RustcLangItemPointeeSized -> 2
  | RustcLangItemUnsize -> 3
  | RustcLangItemAlignOf -> 4
  | RustcLangItemSizeOf -> 5
  | RustcLangItemOffsetOf -> 6
  | RustcLangItemStructuralPeq -> 7
  | RustcLangItemCopy -> 8
  | RustcLangItemClone -> 9
  | RustcLangItemCloneFn -> 10
  | RustcLangItemUseCloned -> 11
  | RustcLangItemTrivialClone -> 12
  | RustcLangItemSync -> 13
  | RustcLangItemDiscriminantKind -> 14
  | RustcLangItemDiscriminant -> 15
  | RustcLangItemPointeeTrait -> 16
  | RustcLangItemMetadata -> 17
  | RustcLangItemDynMetadata -> 18
  | RustcLangItemNonNull -> 19
  | RustcLangItemFreeze -> 20
  | RustcLangItemUnsafeUnpin -> 21
  | RustcLangItemFnPtrTrait -> 22
  | RustcLangItemFnPtrAsPtr -> 23
  | RustcLangItemFnPtrFromPtr -> 24
  | RustcLangItemCode -> 25
  | RustcLangItemDrop -> 26
  | RustcLangItemDestruct -> 27
  | RustcLangItemAsyncDrop -> 28
  | RustcLangItemAsyncDropInPlace -> 29
  | RustcLangItemCoerceUnsized -> 30
  | RustcLangItemDispatchFromDyn -> 31
  | RustcLangItemTryAsDyn -> 32
  | RustcLangItemTransmuteOpts -> 33
  | RustcLangItemTransmuteTrait -> 34
  | RustcLangItemAdd -> 35
  | RustcLangItemSub -> 36
  | RustcLangItemMul -> 37
  | RustcLangItemDiv -> 38
  | RustcLangItemRem -> 39
  | RustcLangItemNeg -> 40
  | RustcLangItemNot -> 41
  | RustcLangItemBitXor -> 42
  | RustcLangItemBitAnd -> 43
  | RustcLangItemBitOr -> 44
  | RustcLangItemShl -> 45
  | RustcLangItemShr -> 46
  | RustcLangItemAddAssign -> 47
  | RustcLangItemSubAssign -> 48
  | RustcLangItemMulAssign -> 49
  | RustcLangItemDivAssign -> 50
  | RustcLangItemRemAssign -> 51
  | RustcLangItemBitXorAssign -> 52
  | RustcLangItemBitAndAssign -> 53
  | RustcLangItemBitOrAssign -> 54
  | RustcLangItemShlAssign -> 55
  | RustcLangItemShrAssign -> 56
  | RustcLangItemIndex -> 57
  | RustcLangItemIndexMut -> 58
  | RustcLangItemUnsafeCell -> 59
  | RustcLangItemCovariantUnsafeCell -> 60
  | RustcLangItemUnsafePinned -> 61
  | RustcLangItemVaArgSafe -> 62
  | RustcLangItemVaList -> 63
  | RustcLangItemComplex -> 64
  | RustcLangItemDeref -> 65
  | RustcLangItemDerefMut -> 66
  | RustcLangItemDerefPure -> 67
  | RustcLangItemDerefTarget -> 68
  | RustcLangItemReceiver -> 69
  | RustcLangItemReceiverTarget -> 70
  | RustcLangItemLegacyReceiver -> 71
  | RustcLangItemFn -> 72
  | RustcLangItemFnMut -> 73
  | RustcLangItemFnOnce -> 74
  | RustcLangItemFnStatic -> 75
  | RustcLangItemAsyncFn -> 76
  | RustcLangItemAsyncFnMut -> 77
  | RustcLangItemAsyncFnOnce -> 78
  | RustcLangItemAsyncFnOnceOutput -> 79
  | RustcLangItemCallOnceFuture -> 80
  | RustcLangItemCallRefFuture -> 81
  | RustcLangItemAsyncFnKindHelper -> 82
  | RustcLangItemAsyncFnKindUpvars -> 83
  | RustcLangItemFnOnceOutput -> 84
  | RustcLangItemIterator -> 85
  | RustcLangItemFusedIterator -> 86
  | RustcLangItemFuture -> 87
  | RustcLangItemFutureOutput -> 88
  | RustcLangItemAsyncIterator -> 89
  | RustcLangItemCoroutineState -> 90
  | RustcLangItemCoroutine -> 91
  | RustcLangItemCoroutineReturn -> 92
  | RustcLangItemCoroutineYield -> 93
  | RustcLangItemCoroutineResume -> 94
  | RustcLangItemUnpin -> 95
  | RustcLangItemPin -> 96
  | RustcLangItemOrderingEnum -> 97
  | RustcLangItemPartialEq -> 98
  | RustcLangItemPartialOrd -> 99
  | RustcLangItemCVoid -> 100
  | RustcLangItemType -> 101
  | RustcLangItemTypeGeneric -> 102
  | RustcLangItemTypeId -> 103
  | RustcLangItemPanic -> 104
  | RustcLangItemPanicNounwind -> 105
  | RustcLangItemPanicFmt -> 106
  | RustcLangItemPanicDisplay -> 107
  | RustcLangItemConstPanicFmt -> 108
  | RustcLangItemPanicBoundsCheck -> 109
  | RustcLangItemPanicMisalignedPointerDereference -> 110
  | RustcLangItemPanicInfo -> 111
  | RustcLangItemPanicLocation -> 112
  | RustcLangItemPanicImpl -> 113
  | RustcLangItemPanicCannotUnwind -> 114
  | RustcLangItemPanicInCleanup -> 115
  | RustcLangItemPanicAddOverflow -> 116
  | RustcLangItemPanicSubOverflow -> 117
  | RustcLangItemPanicMulOverflow -> 118
  | RustcLangItemPanicDivOverflow -> 119
  | RustcLangItemPanicRemOverflow -> 120
  | RustcLangItemPanicNegOverflow -> 121
  | RustcLangItemPanicShrOverflow -> 122
  | RustcLangItemPanicShlOverflow -> 123
  | RustcLangItemPanicDivZero -> 124
  | RustcLangItemPanicRemZero -> 125
  | RustcLangItemPanicCoroutineResumed -> 126
  | RustcLangItemPanicAsyncFnResumed -> 127
  | RustcLangItemPanicAsyncGenFnResumed -> 128
  | RustcLangItemPanicGenFnNone -> 129
  | RustcLangItemPanicCoroutineResumedPanic -> 130
  | RustcLangItemPanicAsyncFnResumedPanic -> 131
  | RustcLangItemPanicAsyncGenFnResumedPanic -> 132
  | RustcLangItemPanicGenFnNonePanic -> 133
  | RustcLangItemPanicNullPointerDereference -> 134
  | RustcLangItemPanicNullReferenceConstructed -> 135
  | RustcLangItemPanicInvalidEnumConstruction -> 136
  | RustcLangItemPanicCoroutineResumedDrop -> 137
  | RustcLangItemPanicAsyncFnResumedDrop -> 138
  | RustcLangItemPanicAsyncGenFnResumedDrop -> 139
  | RustcLangItemPanicGenFnNoneDrop -> 140
  | RustcLangItemBeginPanic -> 141
  | RustcLangItemFormatArgument -> 142
  | RustcLangItemFormatArguments -> 143
  | RustcLangItemDropGlue -> 144
  | RustcLangItemAllocLayout -> 145
  | RustcLangItemStart -> 146
  | RustcLangItemEhPersonality -> 147
  | RustcLangItemCompilerMove -> 148
  | RustcLangItemCompilerCopy -> 149
  | RustcLangItemOwnedBox -> 150
  | RustcLangItemGlobalAlloc -> 151
  | RustcLangItemPhantomData -> 152
  | RustcLangItemManuallyDrop -> 153
  | RustcLangItemMaybeDangling -> 154
  | RustcLangItemBikeshedGuaranteedNoDrop -> 155
  | RustcLangItemMaybeUninit -> 156
  | RustcLangItemTermination -> 157
  | RustcLangItemTry -> 158
  | RustcLangItemTuple -> 159
  | RustcLangItemSliceLen -> 160
  | RustcLangItemTryTraitFromResidual -> 161
  | RustcLangItemTryTraitFromOutput -> 162
  | RustcLangItemTryTraitBranch -> 163
  | RustcLangItemTryTraitFromYeet -> 164
  | RustcLangItemResidualIntoTryType -> 165
  | RustcLangItemCoercePointeeValidated -> 166
  | RustcLangItemConstParamTy -> 167
  | RustcLangItemPoll -> 168
  | RustcLangItemPollReady -> 169
  | RustcLangItemPollPending -> 170
  | RustcLangItemAsyncGenReady -> 171
  | RustcLangItemAsyncGenPending -> 172
  | RustcLangItemAsyncGenFinished -> 173
  | RustcLangItemResumeTy -> 174
  | RustcLangItemGetContext -> 175
  | RustcLangItemContext -> 176
  | RustcLangItemFuturePoll -> 177
  | RustcLangItemAsyncIteratorPollNext -> 178
  | RustcLangItemIntoAsyncIterIntoIter -> 179
  | RustcLangItemOption -> 180
  | RustcLangItemOptionSome -> 181
  | RustcLangItemOptionNone -> 182
  | RustcLangItemResultOk -> 183
  | RustcLangItemResultErr -> 184
  | RustcLangItemControlFlowContinue -> 185
  | RustcLangItemControlFlowBreak -> 186
  | RustcLangItemIntoFutureIntoFuture -> 187
  | RustcLangItemIntoIterIntoIter -> 188
  | RustcLangItemIteratorNext -> 189
  | RustcLangItemPinNewUnchecked -> 190
  | RustcLangItemRangeFrom -> 191
  | RustcLangItemRangeFull -> 192
  | RustcLangItemRangeInclusiveStruct -> 193
  | RustcLangItemRangeInclusiveNew -> 194
  | RustcLangItemRange -> 195
  | RustcLangItemRangeToInclusive -> 196
  | RustcLangItemRangeTo -> 197
  | RustcLangItemRangeMax -> 198
  | RustcLangItemRangeMin -> 199
  | RustcLangItemRangeSub -> 200
  | RustcLangItemRangeFromCopy -> 201
  | RustcLangItemRangeCopy -> 202
  | RustcLangItemRangeInclusiveCopy -> 203
  | RustcLangItemRangeToInclusiveCopy -> 204
  | RustcLangItemString -> 205
  | RustcLangItemCStr -> 206
  | RustcLangItemContractBuildCheckEnsures -> 207
  | RustcLangItemContractCheckRequires -> 208
  | RustcLangItemDefaultTrait4 -> 209
  | RustcLangItemDefaultTrait3 -> 210
  | RustcLangItemDefaultTrait2 -> 211
  | RustcLangItemDefaultTrait1 -> 212
  | RustcLangItemContractCheckEnsures -> 213
  | RustcLangItemReborrow -> 214
  | RustcLangItemCoerceShared -> 215
  | RustcLangItemFieldRepresentingType -> 216
  | RustcLangItemField -> 217
  | RustcLangItemFieldBase -> 218
  | RustcLangItemFieldType -> 219
  | RustcLangItemFieldOffset -> 220
  | RustcLangItemFrom -> 221
  | RustcLangItemFromFn -> 222
  | RustcLangItemFnPtr -> 223

and hash_layout : layout -> int =
 fun (x : layout) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine
                (HashBasic.combine 0 (hash_size x.size))
                (hash_size x.align))
             ((HashBasic.hash_option hash_discriminator) x.discriminator))
          (hash_inhabited_predicate x.inhabited))
       ((HashBasic.hash_list (HashBasic.hash_option hash_variant_layout))
          x.variant_layouts))
    (hash_repr_options x.repr)

and hash_metadata_value : metadata_value -> int =
 fun (x : metadata_value) ->
  match x with
  | DynSize -> 0
  | DynAlign -> 1
  | SliceLength -> 2

and hash_name : name -> int =
 fun (x : name) -> (HashBasic.hash_list hash_path_elem) x

and hash_offset_expr : offset_expr -> int =
 fun (x : offset_expr) ->
  HashBasic.combine
    (HashBasic.combine 0
       ((HashBasic.hash_option hash_offset_guarantee) x.guarantee))
    ((HashBasic.hash_option HashBasic.hash_int) x.chosen)

and hash_offset_guarantee : offset_guarantee -> int =
 fun (x : offset_guarantee) ->
  match x with
  | AtOffset x0 -> HashBasic.combine 0 (hash_size_expr x0)
  | GuaranteedAlignment x0 -> HashBasic.combine 1 (hash_size_expr x0)
  | ReprCField x0 -> HashBasic.combine 2 (hash_field_predecessor x0)

and hash_path_elem : path_elem -> int =
 fun (x : path_elem) ->
  match x with
  | PeIdent (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 0 (HashBasic.hash_string x0))
        (hash_disambiguator x1)
  | PeImpl x0 -> HashBasic.combine 1 (hash_impl_elem x0)
  | PeInstantiated x0 ->
      HashBasic.combine 2 ((hash_binder hash_generic_args) x0)
  | PeTarget x0 -> HashBasic.combine 3 (HashBasic.hash_string x0)
  | PeBuiltin (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 4 (hash_builtin_path_elem x0))
        (hash_disambiguator x1)

and hash_ptr_metadata : ptr_metadata -> int =
 fun (x : ptr_metadata) ->
  match x with
  | NoMetadata -> 0
  | Length -> 1
  | VTable x0 -> HashBasic.combine 2 (hash_type_decl_ref x0)
  | InheritFrom x0 -> HashBasic.combine 3 (hash_ty x0)

and hash_repr_algorithm : repr_algorithm -> int =
 fun (x : repr_algorithm) ->
  match x with
  | Rust -> 0
  | C -> 1

and hash_repr_options : repr_options -> int =
 fun (x : repr_options) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine 0 (hash_repr_algorithm x.repr_algo))
          ((HashBasic.hash_option hash_alignment_modifier) x.align_modif))
       (HashBasic.hash_bool x.transparent))
    ((HashBasic.hash_option hash_integer_type) x.explicit_discr_type)

and hash_size : size -> int =
 fun (x : size) ->
  HashBasic.combine
    (HashBasic.combine 0 ((HashBasic.hash_option hash_size_expr) x.chosen))
    ((HashBasic.hash_option hash_size_expr) x.guarantee)

and hash_size_expr : size_expr -> int =
 fun (x : size_expr) -> (hash_hash_consed hash_size_expr_kind) x

and hash_size_expr_kind : size_expr_kind -> int =
 fun (x : size_expr_kind) ->
  match x with
  | SizeExprConstant x0 -> HashBasic.combine 0 (hash_constant_expr x0)
  | SizeExprFromMetadata x0 -> HashBasic.combine 1 (hash_metadata_value x0)
  | SizeExprMax x0 ->
      HashBasic.combine 2 ((HashBasic.hash_list hash_size_expr) x0)
  | SizeExprMin x0 ->
      HashBasic.combine 3 ((HashBasic.hash_list hash_size_expr) x0)
  | SizeExprPlus (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 4 (hash_size_expr x0))
        (hash_size_expr x1)
  | SizeExprScale (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 5 (hash_size_expr x0))
        (hash_constant_expr x1)
  | SizeExprAtLeast x0 -> HashBasic.combine 6 (hash_size_expr x0)
  | SizeExprAlignTo (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 7 (hash_size_expr x0))
        (hash_size_expr x1)
  | SizeExprIfInhabited (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 8 (hash_ty x0))
           (hash_size_expr x1))
        (hash_size_expr x2)

and hash_type_decl : type_decl -> int =
 fun (x : type_decl) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine
                (HashBasic.combine
                   (HashBasic.combine
                      (HashBasic.combine 0 (hash_type_decl_id x.def_id))
                      (hash_item_meta x.item_meta))
                   (hash_generic_params x.generics))
                (hash_type_source x.src))
             (hash_type_decl_kind x.kind))
          ((HashBasic.hash_list (fun (k, v) ->
                HashBasic.combine (HashBasic.hash_string k) (hash_layout v)))
             x.layout))
       (hash_ptr_metadata x.ptr_metadata))
    ((HashBasic.hash_option hash_implements_marker_traits) x.marker_traits)

and hash_type_decl_kind : type_decl_kind -> int =
 fun (x : type_decl_kind) ->
  match x with
  | Struct x0 -> HashBasic.combine 0 ((HashBasic.hash_list hash_field) x0)
  | Enum x0 -> HashBasic.combine 1 ((HashBasic.hash_list hash_variant) x0)
  | Union x0 -> HashBasic.combine 2 ((HashBasic.hash_list hash_field) x0)
  | Opaque -> 3
  | Alias x0 -> HashBasic.combine 4 (hash_ty x0)
  | TDeclError x0 -> HashBasic.combine 5 (HashBasic.hash_string x0)

and hash_type_source : type_source -> int =
 fun (x : type_source) ->
  match x with
  | NormalType -> 0
  | ClosureType x0 -> HashBasic.combine 1 (hash_closure_info x0)
  | VTableType (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 2 (hash_dyn_predicate x0))
           ((HashBasic.hash_list hash_v_table_field) x1))
        ((HashBasic.hash_list (HashBasic.hash_option hash_field_id)) x2)
  | BuiltinType x0 -> HashBasic.combine 3 (hash_builtin_adt x0)

and hash_v_table_field : v_table_field -> int =
 fun (x : v_table_field) ->
  match x with
  | VTableSize -> 0
  | VTableAlign -> 1
  | VTableDrop -> 2
  | VTableMethod x0 -> HashBasic.combine 3 (hash_trait_method_id x0)
  | VTableSuperTrait x0 -> HashBasic.combine 4 (hash_trait_clause_id x0)

and hash_variant : variant -> int =
 fun (x : variant) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine
             (HashBasic.combine
                (HashBasic.combine 0 (hash_variant_id x.id))
                (hash_span x.span))
             (hash_attr_info x.attr_info))
          (HashBasic.hash_string x.variant_name))
       ((HashBasic.hash_list hash_field) x.fields))
    (hash_integer_value x.discriminant)

and hash_variant_layout : variant_layout -> int =
 fun (x : variant_layout) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0
          ((HashBasic.hash_list hash_offset_expr) x.field_offsets))
       (hash_inhabited_predicate x.inhabited))
    ((HashBasic.hash_list (fun (x0, x1) ->
          HashBasic.combine
            (HashBasic.combine 0 (HashBasic.hash_int x0))
            (hash_integer_value x1)))
       x.tagger)
