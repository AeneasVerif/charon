(** WARNING: this file is partially auto-generated. Do not edit `GAst.ml` by
    hand. Edit `GAst.template.ml` instead, or improve the code generation tool
    so avoid the need for hand-writing things.

    `GAst.template.ml` contains the manual definitions and some `(* __REPLACEn__
    *)` comments. These comments are replaced by auto-generated definitions by
    running `make generate-asts` in the crate root. The code-generation code is
    in `charon/src/bin/generate-asts`. *)

open Generated_Types
open Generated_Meta
open Generated_Expressions
open Identifiers
module FunDeclId = Expressions.FunDeclId
module GlobalDeclId = Expressions.GlobalDeclId
module TraitDeclId = Types.TraitDeclId
module TraitImplId = Types.TraitImplId
module TraitClauseId = Types.TraitClauseId
module BranchId = IdGen ()

(* Imports *)
type builtin_fun_id = Types.builtin_fun_id [@@deriving show, ord]
type fun_id = Types.fun_id [@@deriving show, ord]
type fn_ptr_kind = Types.fn_ptr_kind [@@deriving show, ord]
type fun_decl_id = Types.fun_decl_id [@@deriving show, ord]

(** (U)LLBC is a language with side-effects: a statement may abort in a way that
    isn't tracked by control-flow. The three kinds of abort are:
    - Panic
    - Undefined behavior (caused by an "assume")
    - Unwind termination *)
type abort_kind =
  | Panic of name option
      (** A built-in panicking function, or a panic due to a failed built-in
          check (e.g. for out-of-bounds accesses). *)
  | UndefinedBehavior  (** Undefined behavior in the rust abstract machine. *)
  | UnwindTerminate
      (** Unwind had to stop for ABI reasons or because cleanup code panicked
          again. *)

(** Check the value of an operand and abort if the value is not expected. This
    is introduced to avoid a lot of small branches.

    We translate MIR asserts (introduced for out-of-bounds accesses or divisions
    by zero for instance) to this. We then eliminate them in
    [crate::transform::resugar::reconstruct_fallible_operations], because
    they're implicit in the semantics of our array accesses etc. Finally we
    introduce new asserts in [crate::transform::resugar::reconstruct_asserts].
*)
and assertion = {
  cond : operand;
  expected : bool;
      (** The value that the operand should evaluate to for the assert to
          succeed. *)
  check_kind : builtin_assert_kind option;
      (** The kind of check performed by this assert. This is only used for
          error reporting, as the check is actually performed by the
          instructions preceding the assert. *)
}

(** Statements that only affect borrow-checking. They are no-ops at runtime. *)
and borrowck_statement =
  | FakeRead of place  (** Acts like a read of the place. *)
  | SetType of place * ty * variance
      (** Relate the type of a place to the provided type. For example,
          [let x: Self = value] produces [SetType] for [x] and [Self].

          Fields:
          - [place]
          - [ty]
          - [variance] *)
  | SetOutlives of ty * region
      (** Require a type to outlive a region. For example, the ['a] bound in
          [let x: impl Copy + 'a = value] produces [SetOutlives(typeof(x), 'a)].
      *)
  | PredicateHolds of trait_ref
      (** Require a trait predicate to hold. For example, the [Copy] bound in
          [let x: impl Copy = value] produces [PredicateHolds(typeof(x): Copy)].
      *)

and branch_id = (BranchId.id[@visitors.opaque])

(** The kind of a built-in assertion, which may panic and unwind. These are
    removed by [reconstruct_fallible_operations] because they're implicit in the
    semantics of (U)LLBC. This kind should only be used for error-reporting
    purposes, as the check itself is performed in the instructions preceding the
    assert. *)
and builtin_assert_kind =
  | BoundsCheck of operand * operand
      (** Fields:
          - [len]
          - [index] *)
  | Overflow of binop * operand * operand
  | OverflowNeg of operand
  | DivisionByZero of operand
  | RemainderByZero of operand
  | MisalignedPointerDereference of operand * operand
      (** Fields:
          - [required]
          - [found] *)
  | NullPointerDereference
  | NullReferenceCreated
  | InvalidEnumConstruction of operand
  | ResumedAfterReturn
  | ResumedAfterPanic
  | ResumedAfterDrop

and call = { func : fn_operand; args : operand list; dest : place }

(** A [Drop] statement/terminator can mean two things, depending on what MIR
    phase we retrieved from rustc: it could be a real drop, or it could be a
    "conditional drop", which is where drop may happen depending on whether the
    borrow-checker determines a drop is needed. *)
and drop_kind =
  | Precise
      (** A real drop. This calls [<T as Destruct>::drop_glue(&mut place)] and
          marks the place as moved-out-of. Use [--desugar-drops] to transform
          all such drops to an actual function call.

          The [drop_glue] method is added by Charon to the [Destruct] trait to
          make it possible to track drop code in polymorphic code. It contains
          the same code as the [core::ptr::drop_glue<T>] builtin would.

          Drop are precise in MIR [elaborated] and [optimized]. *)
  | Conditional
      (** A conditional drop, which may or may not end up running drop code
          depending on the code path that led to it. A conditional drop may also
          become a partial drop (dropping only the subplaces that haven't been
          moved out of), may be conditional on the code path that led to it, or
          become an async drop. The exact semantics are left intentionally
          unspecified by rustc developers. To elaborate such drops into precise
          drops, pass [--precise-drops] to Charon.

          A conditional drop may also be passed an unaligned place when dropping
          fields of packed structs. Such a thing is UB for a precise drop.

          Drop are conditional in MIR [built] and [promoted]. *)

(** Common error used during the translation. *)
and error = { span : span; msg : string }

(** A function operand is used in function calls. It either designates a
    top-level function, or a place in case we are using function pointers stored
    in local variables. *)
and fn_operand =
  | FnOpRegular of fn_ptr
      (** Regular case: call to a top-level function, trait method, etc. *)
  | FnOpDynamic of operand  (** Use of a function pointer. *)

(** Where a given function came from. *)
and fun_source =
  | NormalFun  (** A normal function. *)
  | TraitDefaultFun of trait_decl_ref * trait_method_id
      (** A default method in a trait declaration.

          Fields:
          - [trait_ref]: The trait declaration this item belongs to.
          - [item_id]: The method this corresponds to. *)
  | TraitImplFun of trait_impl_ref * trait_decl_ref * trait_method_id * bool
      (** A method in a trait implementation.

          Fields:
          - [impl_ref]: The trait implementation the method belongs to.
          - [trait_ref]: The trait declaration that the impl block implements.
          - [item_id]: The method this corresponds to.
          - [reuses_default]: True if the trait decl had a default
            implementation for this method and this item is a copy of the
            default item. *)
  | VTableShimFun
      (** Wraps a concrete implementation of a method into a function that takes
          [dyn Trait] as its [Self] type. This shim casts the receiver to the
          known concrete type and calls the real method. *)
  | GlobalInitializerFun of global_decl_ref
      (** The initializer for a global. *)
  | TargetDependentFun of fun_decl_ref
      (** A target-specific variant behind a [TargetDispatch] façade. The
          dispatcher is the function with the [Body::TargetDispatch] body that
          dispatches to this function.

          Fields:
          - [dispatcher] *)

(** Where a given global came from. *)
and global_source =
  | NormalGlobal  (** A normal global. *)
  | TraitDefaultGlobal of trait_decl_ref * assoc_const_id
      (** A default assoc const in a trait declaration.

          Fields:
          - [trait_ref]: The trait declaration the const belongs to.
          - [item_id]: The associated const this corresponds to. *)
  | TraitImplGlobal of trait_impl_ref * trait_decl_ref * assoc_const_id * bool
      (** An associated const in a trait implementation.

          Fields:
          - [impl_ref]: The trait implementation the const belongs to.
          - [trait_ref]: The trait declaration that the impl block implements.
          - [item_id]: The associated const this corresponds to.
          - [reuses_default]: True if the trait decl had a default value for
            this const and this item is a copy of the default item. *)
  | VTableInstanceGlobal of trait_impl_ref option
      (** Defines the vtable for a trait impl.

          Fields:
          - [impl_ref]: The originating impl. This is [None] in monomorphized
            mode: the vtable global itself identifies the concrete
            instantiation, so we don't translate an impl reference solely to
            record its provenance. *)

(** A variable *)
and local = {
  index : local_id;  (** Unique index identifying the variable *)
  name : string option;
      (** Variable name - may be [None] if the variable was introduced by Rust
          through desugaring. *)
  span : span;  (** Span of the variable declaration. *)
  local_ty : ty;  (** The variable type *)
}

(** The local variables of a body. *)
and locals = {
  arg_count : int;
      (** The number of local variables used for the input arguments. *)
  locals : local list;
      (** The local variables. We always have, in the following order:
          - the local used for the return value (index 0)
          - the [arg_count] input arguments
          - the remaining locals, used for the intermediate computations *)
}

(** A branching operation. *)
and switch_data = {
  scrutinee : switch_scrutinee;  (** The value to branch over. *)
  branches : (constant_expr * branch_id) list;
      (** Which branch to take for each value of the scrutinee. Several values
          may point to the same branch, and not all values may be accounted for.

          If the scrutinee is an operand, the constant expressions are literal
          values. If the scrutinee is a discriminant read, the expressions are
          of the form [ConstantExprKind::Discriminant]. *)
  fallback : branch_id option;
      (** Branch to use if the scrutinee didn't match any of the values above.
          [None] if the set of branch values is known to be exhaustive. *)
}

(** The value inspected by a switch. Must be of integer, bool or char type. *)
and switch_scrutinee =
  | SwitchValue of operand  (** Inspect the value produced by an operand. *)
  | SwitchDiscriminant of place
      (** Inspect the discriminant of an enum place. *)
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_fun_sig";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_rvalue" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_fun_sig";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_rvalue" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

(** A global variable definition (constant or static). *)
type global_decl = {
  def_id : global_decl_id;
  item_meta : item_meta;  (** The meta data associated with the declaration. *)
  generics : generic_params;
  ty : ty;
  src : global_source;
      (** The context of the global: distinguishes normal items from
          trait-associated items and vtable instances. *)
  global_kind : global_kind;  (** The kind of global (static or const). *)
  value : constant_expr;
      (** The value of this constant/static. By default this is a
          [[ConstantExprKind::Call]] to the initializer function that computes
          the value (the function uses the same generic parameters as the
          global). *)
}

and global_kind =
  | Static  (** A static. *)
  | ThreadLocal  (** A thread-local static. *)
  | NamedConst
      (** A const with a name (either top-level or an associated const in a
          trait). *)
  | AnonConst
      (** A const without a name:
          - An inline const expression ([const { 1 + 1 }]);
          - A const expression in a type ([[u8; sizeof::<T>()]]);
          - A promoted constant, automatically lifted from a body ([&0]). *)
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_global_decl";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_fun_sig" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_global_decl";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_fun_sig" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

class ['self] iter_trait_decl_base =
  object (self : 'self)
    inherit [_] iter_global_decl

    method visit_trait_method_id_map :
        'a. ('env -> 'a -> unit) -> 'env -> 'a trait_method_id_map -> unit =
      TraitMethodId.Map.visit_iter
  end

class ['self] map_trait_decl_base =
  object (self : 'self)
    inherit [_] map_global_decl

    method visit_trait_method_id_map :
        'a 'b.
        ('env -> 'a -> 'b) ->
        'env ->
        'a trait_method_id_map ->
        'b trait_method_id_map =
      TraitMethodId.Map.visit_map
  end

(** An associated constant in a trait. *)
type trait_assoc_const = {
  name : trait_item_name;
  attr_info : attr_info;
  ty : ty;
  default : global_decl_ref option;
}

(** An associated type in a trait. *)
and trait_assoc_ty = {
  name : trait_item_name;
  attr_info : attr_info;
  default : trait_assoc_ty_impl option;
  implied_clauses : trait_param list;
      (** List of trait clauses that apply to this type. *)
}

(** A trait **declaration**.

    For instance:
    {@rust[
      trait Foo {
        type Bar;

        fn baz(...); // required method (see below)

        fn test() -> bool { true } // provided method (see below)
      }
    ]}

    In case of a trait declaration, we don't include the provided methods (the
    methods with a default implementation): they will be translated on a
    per-need basis. This is important for two reasons:
    - this makes the trait definitions a lot smaller (the Iterator trait has
      *one* declared function and more than 70 provided functions)
    - this is important for the external traits, whose provided methods often
      use features we don't support yet

    Remark: In Aeneas, we still translate the provided methods on an individual
    basis, and in such a way thay they take as input a trait instance. This
    means that we can use default methods *but*:
    - implementations of required methods shoudln't call default methods
    - trait implementations shouldn't redefine required methods

    The use case we have in mind is [std::iter::Iterator]: it declares one
    required method ([next]) that should be implemented for every iterator, and
    defines many helpers like [all], [map], etc. that shouldn't be
    re-implemented. Of course, this forbids other useful use cases such as
    visitors implemented by means of traits. *)
and trait_decl = {
  def_id : trait_decl_id;
  item_meta : item_meta;
  src : trait_decl_source;
      (** Distinguishes normal traits from trait aliases. *)
  generics : generic_params;
  implied_clauses : trait_param list;
      (** The "parent" clauses: the supertraits.

          Supertraits are actually regular where clauses, but we decided to have
          a custom treatment.
          {@rust[
            trait Foo : Bar {
                        ^^^
                    supertrait, that we treat as a parent predicate
            }
          ]}
          TODO: actually, as of today, we consider that all trait clauses of
          trait declarations are parent clauses. *)
  consts : trait_assoc_const assoc_const_id_map;
      (** The associated constants declared in the trait. *)
  types : trait_assoc_ty binder assoc_type_id_map;
      (** The associated types declared in the trait. The binder binds the
          generic parameters of the type if it is a GAT (Generic Associated
          Type). For a plain associated type the binder binds nothing. *)
  methods : trait_method binder trait_method_id_map;
      (** The methods declared by the trait. The binder binds the generic
          parameters of the method.

          {@rust[
            rust
            trait Trait<T> {
              // The [Binder] for this method binds ['a] and [U].
              fn method<'a, U>(x: &'a U);
            }
          ]} *)
  vtable : type_decl_ref option;
      (** The virtual table struct for this trait, if it has one. It is
          guaranteed that the trait has a vtable iff it is dyn-compatible. *)
}

(** Where the trait comes from. *)
and trait_decl_source =
  | NormalTraitDecl  (** A regular trait. *)
  | TraitAliasTraitDecl  (** The trait declaration coming from a trait alias. *)

and trait_item_name = string

(** A trait method. *)
and trait_method = {
  name : trait_item_name;
  item_meta : item_meta;
  signature : fun_sig;
  default : fun_decl_ref option;
      (** The default method implementation, if there is one. *)
}
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_trait_decl";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_trait_decl_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_trait_decl";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_trait_decl_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

(** An expression body. TODO: arg_count should be stored in GFunDecl below. But
    then, the print is obfuscated and Aeneas may need some refactoring. *)
type 'a0 gexpr_body = {
  span : span;
  bound_body_regions : int;
      (** The number of regions existentially bound in this body. We introduce
          fresh such regions during translation instead of the erased regions
          that rustc gives us. *)
  locals : locals;  (** The local variables. *)
  body : 'a0;  (** The statements and blocks that compose this body. *)
}

(** A trait **implementation**.

    For instance:
    {@rust[
      impl Foo for List {
        type Bar = ...

        fn baz(...) { ... }
      }
    ]} *)
and trait_impl = {
  def_id : trait_impl_id;
  item_meta : item_meta;
  src : trait_impl_source;
  impl_trait : trait_decl_ref;
      (** The information about the implemented trait. Note that this contains
          the instantiation of the "parent" clauses. *)
  generics : generic_params;
  implied_trait_refs : trait_ref list;
      (** The trait references for the parent clauses (see [TraitDecl]). *)
  consts : global_decl_ref assoc_const_id_map;
      (** The implemented associated constants. *)
  types : trait_assoc_ty_impl binder assoc_type_id_map;
      (** The implemented associated types. *)
  methods : fun_decl_ref binder trait_method_id_map;
      (** The implemented methods *)
  vtable : global_decl_ref option;
      (** The virtual table instance for this trait implementation. This is
          [Some] iff the trait is dyn-compatible. *)
}

(** Where the impl comes from. *)
and trait_impl_source =
  | NormalTraitImpl  (** A regular trait implementation. *)
  | TraitAliasTraitImpl
      (** The blanket implementation generated for a trait alias. *)
  | ClosureTraitImpl of closure_kind
      (** An implementation of one of the [Fn*] traits, generated for a closure.

          Fields:
          - [kind] *)
  | DestructTraitImpl
      (** The [Destruct] implementation generated for an ADT or closure. *)
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_trait_impl";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_trait_decl" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_trait_impl";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_trait_decl" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]
