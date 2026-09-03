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
type literal_type = Values.literal_type [@@deriving show, ord, eq]

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
      ancestors = [ "iter_literal" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_type_vars";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_literal" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "reduce_type_vars";
      monomorphic = [ "env" ];
      variety = "reduce";
      ancestors = [ "reduce_literal" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "mapreduce_type_vars";
      monomorphic = [ "env" ];
      variety = "mapreduce";
      ancestors = [ "mapreduce_literal" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

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

(** A built-in function, representing a specific built-in function that's part
    of the LLBC semantics. *)
and builtin_fun_id =
  | ArrayToSliceShared
      (** Cast [&[T; N]] to [&[T]].

          This is used instead of unsizing coercions when
          [--ops-to-function-calls] is set. *)
  | ArrayToSliceMut
      (** Cast [&mut [T; N]] to [&mut [T]].

          This is used instead of unsizing coercions when
          [--ops-to-function-calls] is set. *)
  | ArrayRepeat
      (** [repeat(n, x)] returns an array where [x] has been replicated [n]
          times.

          This is used instead of [Rvalue::ArrayRepeat] when
          [--ops-to-function-calls] is set. *)
  | Index of builtin_index_op
      (** A built-in funciton introduced instead of array/slice place indexing
          when [--index-to-function-calls] is set. The signature depends on the
          parameters. It could look like:
          - [fn ArrayIndexShared<T,N>(&[T;N], usize) -> &T]
          - [fn SliceIndexShared<T>(&[T], usize) -> &T]
          - [fn ArraySubSliceShared<T,N>(&[T;N], usize, usize) -> &[T]]
          - [fn SliceSubSliceMut<T>(&mut [T], usize, usize) -> &mut [T]]
          - etc *)
  | PtrFromParts of ref_kind
      (** Build a raw pointer, from a data pointer and metadata. The metadata
          can be unit, if building a thin pointer.

          This is used instead of [AggregateKind::RawPtr] when
          [--ops-to-function-calls] is set. *)

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

(** One of 8 built-in indexing operations. *)
and builtin_index_op = {
  is_array : bool;  (** Whether this is a slice or array. *)
  mutability : ref_kind;
      (** Whether we're indexing mutably or not. Determines the type ofreference
          of the input and output. *)
  is_range : bool;
      (** Whether we're indexing a single element or a subrange. If [true], the
          function takes two indices and the output is a slice; otherwise, the
          function take one index and the output is a reference to a single
          element. *)
}

(** Builtin types identifiers.

    WARNING: for now, all the built-in types are covariant in the generic
    parameters (if there are). Adding types which don't satisfy this will
    require to update the code abstracting the signatures (to properly take into
    account the lifetime constraints).

    TODO: update to not hardcode the types (except [Box] maybe) and be more
    modular. TODO: move to builtins.rs? *)
and builtin_ty =
  | TTuple  (** A tuple [(A, B, ...)], including [unit]. *)
  | TBox
      (** Boxes; always detected, though they are only treated as primitives
          with [--treat-box-as-builtin] *)
  | TStr
      (** The [str] type, which corresponds to a [[u8]] that encodes a string
          with UTF-8. *)

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
  | CLiteral of literal
  | CAdt of variant_id option * constant_expr list
      (** In most situations: Enumeration with one variant with no fields,
          structure with no fields, unit (encoded as a 0-tuple).

          Less frequently: arbitrary ADT values.

          We eliminate this case in a micro-pass. *)
  | CArray of constant_expr list
  | CGlobal of global_decl_ref
      (** The value is a top-level constant/static.

          We eliminate this case in a micro-pass.

          Remark: constants can actually have generic parameters.
          {@rust[
            struct V<const N: usize, T> {
              x: [T; N],
            }

            impl<const N: usize, T> V<N, T> {
              const LEN: usize = N; // This has generics <N, T>
            }

            fn use_v<const N: usize, T>(v: V<N, T>) {
              let l = V::<N, T>::LEN; // We need to provided a substitution here
            }
          ]} *)
  | CTraitConst of trait_ref * assoc_const_id
      (** A trait associated constant.

          Ex.:
          {@rust[
            impl Foo for Bar {
              const C : usize = 32; // <-
            }
          ]} *)
  | CVTableRef of trait_ref
      (** A reference to the vtable [static] item for this trait ref. This can
          be normalized for cases where we do emit a vtable item. That's not
          always the case for builtin traits, e.g. for [MetaSized]. *)
  | CDiscriminant of type_decl_ref * variant_id
      (** The integer discriminant value corresponding to this enum variant. *)
  | CRef of constant_expr * unsizing_metadata option
      (** A shared reference to a constant value.

          We eliminate this case in a micro-pass. *)
  | CPtr of ref_kind * constant_expr * unsizing_metadata option
      (** A pointer to a mutable static.

          We eliminate this case in a micro-pass. *)
  | CVar of const_generic_var_id de_bruijn_var  (** A const generic var *)
  | CCall of fn_ptr * constant_expr list
      (** A call to a [const fn] or a constant's initializer. *)
  | CFnDef of fn_ptr  (** Function definition -- this is a ZST constant *)
  | CFnPtr of fn_ptr
      (** A function pointer to a function item; this is an actual pointer to
          that function item.

          We eliminate this case in a micro-pass. *)
  | CSizeOf of ty  (** The size of the given type. *)
  | CAlignOf of ty  (** The alignment of the given type. *)
  | CTypeId of ty  (** The [TypeId] value for a type. *)
  | CPtrNoProvenance of big_int
      (** A pointer with no provenance (e.g. 0 for the null pointer)

          We eliminate this case in a micro-pass. *)
  | CRawMemory of byte list
      (** Raw memory value obtained from constant evaluation. Used when a more
          structured representation isn't possible (e.g. for unions) or just
          isn't implemented yet. *)
  | COpaque of string
      (** A constant expression that Charon still doesn't handle, along with the
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
  | FunId of fun_id
  | TraitMethod of trait_ref * trait_method_id
      (** If a trait: the reference to the trait and the id of the trait method.
      *)

(** Reference to a function declaration. *)
and fun_decl_ref = {
  id : fun_decl_id;
  generics : generic_args;  (** Generic arguments passed to the function. *)
}

(** A regular or builtin function. *)
and fun_id =
  | FRegular of fun_decl_id
      (** A "regular" function (function local to the crate, external function
          not treated as a primitive one). *)
  | FBuiltin of builtin_fun_id
      (** A primitive function, coming from a standard library (for instance:
          [alloc::boxed::Box::new]). TODO: rename to "Primitive" *)

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
  trait_refs : trait_ref list;
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
  | ProvFunction of fun_decl_ref
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

(** A value of type [T] bound by regions. We should use [binder] instead but
    this causes name clash issues in the derived ocaml visitors. *)
and 'a0 region_binder = {
  binder_regions : region_param list;
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
  implied_trait_refs : trait_ref list;
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

(** A reference to a trait.

    This type is hash-consed, [TraitRefContents] contains the actual data. *)
and trait_ref = trait_ref_contents hash_consed

and trait_ref_contents = {
  kind : trait_ref_kind;
  trait_decl_ref : trait_decl_ref region_binder;
      (** Not necessary, but useful *)
}

(** Identifier of a trait instance. This is derived from the trait resolution.

    Should be read as a path inside the trait clauses which apply to the current
    definition. Note that every path designated by [TraitInstanceId] refers to a
    *trait instance*, which is why the [[TraitRefKind::Clause]] variant may seem
    redundant with some of the other variants. *)
and trait_ref_kind =
  | TraitImpl of trait_impl_ref
      (** A specific top-level implementation item. *)
  | Clause of trait_clause_id de_bruijn_var
      (** One of the local clauses.

          Example:
          {@rust[
            fn f<T>(...) where T : Foo
                               ^^^^^^^
                               Clause(0)
          ]} *)
  | ParentClause of trait_ref * trait_clause_id
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
  | ItemClause of trait_ref * assoc_type_id * trait_clause_id
      (** A clause defined on an associated type. This variant is only used
          during translation; after the [lift_associated_item_clauses] pass,
          clauses on items become [ParentClause]s.

          Example:
          {@rust[
            trait Foo {
              type W: Bar0 + Bar1 // Bar1 contains a method bar1
                             ^^^^
                          this is the clause 1 applying to W
            }

            fn f<T : Foo>(x : T::W) {
              x.bar1();
              ^^^^^^^
              ItemClause(Clause(0), W, 1)
                                    ^^^^
                                    clause 1 from item W (from local clause 0)
            }
          ]} *)
  | Self
      (** The implicit [Self: Trait] clause. Present inside trait declarations,
          including trait method declarations. Not present in trait
          implementations as we can use [TraitImpl] intead. *)
  | BuiltinOrAuto of
      builtin_impl_data
      * trait_ref list
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

(** A type. *)
and ty = ty_kind hash_consed

and ty_kind =
  | TAdt of type_decl_ref
      (** An ADT. Note that here ADTs are very general. They can be:
          - user-defined ADTs
          - tuples (including [unit], which is a 0-tuple)
          - built-in types, namely [Box] and [str]

          Note: this is incorrectly named: this can refer to any valid
          [TypeDecl] including extern types. *)
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
          the second branch will have type [Never]. Also note that [Never] can
          be coerced to any type.

          Note that we eliminate the variables which have this type in a
          micro-pass. As statements don't have types, this type disappears
          eventually disappears from the AST. *)
  | TRef of region * ty * ref_kind  (** A borrow *)
  | TRawPtr of ty * ref_kind  (** A raw pointer. *)
  | TTraitType of trait_ref * assoc_type_id * generic_args
      (** A trait associated type

          Ex.:
          {@rust[
            trait Foo {
              type Bar; // type associated to the trait Foo
            }
          ]} *)
  | TDynTrait of dyn_predicate  (** [dyn Trait] *)
  | TFnPtr of fun_sig region_binder
      (** Function pointer type. This is a literal pointer to a region of memory
          that contains a callable function. This is a function signature with
          limited generics: it only supports lifetime generics, not other kinds
          of generics. *)
  | TFnDef of fn_ptr region_binder
      (** The unique type associated with each function item. Each function item
          is given a unique generic type that takes as input the function's
          early-bound generics. This type is not generally nameable in Rust;
          it's a ZST (there's a unique value), and a value of that type can be
          cast to a function pointer or passed to functions that expect
          [FnOnce]/[FnMut]/[Fn] parameters. There's a binder here because charon
          function items take both early and late-bound lifetimes as arguments;
          given that the type here is polymorpohic in the late-bound variables
          (those that could appear in a function pointer type like
          [for<'a> fn(&'a u32)]), we need to bind them here. *)
  | TPtrMetadata of ty
      (** As a marker of taking out metadata from a given type The internal type
          is assumed to be a type variable *)
  | TArray of ty * constant_expr  (** An array type [[T; N]] *)
  | TSlice of ty  (** A slice type [[T]] *)
  | TPattern of ty * type_pattern
      (** A pattern type. This is a newtype over the first type whose valid
          values are restricted by the pattern. *)
  | TError of string  (** A type that could not be computed or was incorrect. *)

(** Reference to a type declaration.

    This includes user-defined ADTs (structs, enums, unions), but also tuples,
    boxes, and [str], which we translate as [struct str([u8])]. *)
and type_decl_ref = {
  id : type_decl_id;
  generics : generic_args;
  builtin : builtin_ty option;
      (** If this points to a built-in type, it is recorded here for easier
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
  | MetaVTable of trait_ref * constant_expr
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
      * (scalar_value range_inclusive * discriminator) list
      * discriminator
      (** Branch on an integer value read from memory at [offset].

          Fields:
          - [offset]: Byte offset to read from.
          - [int_ty]: Integer type to read.
          - [children]: If the integer is in one of these ranges, continue with
            the given [Discriminator]. The ranges are sorted.
          - [fallback]: Fallback if no range in [children] matches. *)

(** An expression that represents a size in bytes. *)
and exact_size_expr = exact_size_expr_kind hash_consed

and exact_size_expr_kind =
  | ExactSizeExprConstant of constant_expr
      (** An arbitrary constant of type [usize]. *)
  | ExactSizeExprFromMetadata of metadata_value
      (** Layout information stored in the pointer metadata to this object. *)
  | ExactSizeExprMax of exact_size_expr list
  | ExactSizeExprMin of exact_size_expr list
  | ExactSizeExprPlus of exact_size_expr * exact_size_expr
  | ExactSizeExprScale of exact_size_expr * constant_expr
  | ExactSizeExprAlignTo of exact_size_expr * exact_size_expr
      (** The next multiple of [target_align] from [base].

          Fields:
          - [base]
          - [target_align] *)
  | ExactSizeExprIfInhabited of ty * exact_size_expr * exact_size_expr
      (** A size expression that depens on whether the given type is inhabited.

          Fields:
          - [ty]
          - [then_size]
          - [else_size] *)

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
  | RustcLangItemFreeze  (**The [freeze] lang item. *)
  | RustcLangItemUnsafeUnpin  (**The [unsafe_unpin] lang item. *)
  | RustcLangItemFnPtrTrait  (**The [fn_ptr_trait] lang item. *)
  | RustcLangItemFnPtrAddr  (**The [fn_ptr_addr] lang item. *)
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
  | RustcLangItemPin  (**The [pin] lang item. *)
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

(** Type layout information.

    Does not include information about niches. If the type does not have a fully
    known layout (e.g. it is ?Sized) some of the layout parts are not available.
*)
and layout = {
  size : size_expr;  (** The size of the type in bytes. *)
  align : size_expr;  (** The alignment, in bytes. *)
  discriminator : discriminator option;
      (** Decision tree that determines the active variant by reading memory.
          Only [Some] for enums. *)
  uninhabited : bool;
      (** Whether the type is uninhabited, i.e. has any valid value at all. Note
          that uninhabited types can have arbitrary layouts: [(u32, !)] has
          space for the [u32] and [enum E2 { A, B(!), C(i32, !) }] may have
          space for a discriminant. *)
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
  | AtOffsetZero
      (** Guaranteed to be at offset zero. This applies for [repr(transparent)]
          and in some [repr(C)] cases. *)
  | GuaranteedAlignment of exact_size_expr
      (** Guaranteed only to be aligned to the given expression. *)
  | ReprCField of field_id option
      (** This offset is computed by the layout algorithm for C: take the
          previous field offset, add the previous field size, and align to the
          current field alignment.

          Fields:
          - [predecessor]: If this is [None], then the field is directly after
            the enum tag. *)

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
  explicit_discr_type : literal_type option;
      (** The type supplied to [repr(..)], if any. *)
}

(** An expression denoting a size in bytes. *)
and size_expr = {
  guarantee : size_guarantee option;
      (** The guarantees about this size that can be relied on according to the
          Rust Reference. *)
  chosen : int option;
      (** The size chosen by this rustc run. [None] for unsized types. *)
}

(** Guaranteed facts about a layout size. *)
and size_guarantee = Equals of exact_size_expr | AtLeast of exact_size_expr

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
  | BuiltinType of builtin_ty
      (** A type declaration synthesised for a builtin type. *)

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
  discriminant : literal;
      (** The discriminant value outputted by [std::mem::discriminant] for this
          variant. This can be different than the value stored in memory (called
          [tag]); that one is described by [[Discriminator]] and
          [[VariantLayout::tagger]]. *)
}

(** Simplified layout of a single variant.

    Maps fields to their offset within the layout. *)
and variant_layout = {
  field_offsets : offset_expr list;  (** The offset of each field. *)
  uninhabited : bool;
      (** Whether the variant is uninhabited, i.e. has any valid possible value.
          Note that uninhabited types can have arbitrary layouts. *)
  tagger : (int * scalar_value) list;
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
