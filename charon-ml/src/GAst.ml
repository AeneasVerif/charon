(** WARNING: this file is partially auto-generated. Do not edit `GAst.ml`
    by hand. Edit `GAst.template.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `GAst.template.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

(** Definitions shared between the ULLBC and the LLBC ASTs. *)
open Types

open Meta
open Expressions
module FunDeclId = Expressions.FunDeclId
module GlobalDeclId = Expressions.GlobalDeclId
module TraitDeclId = Types.TraitDeclId
module TraitImplId = Types.TraitImplId
module TraitClauseId = Types.TraitClauseId

(* Imports *)
type builtin_fun_id = Expressions.builtin_fun_id [@@deriving show, ord]
type fun_id = Expressions.fun_id [@@deriving show, ord]

type fun_id_or_trait_method_ref = Expressions.fun_id_or_trait_method_ref
[@@deriving show, ord]

(** A variable *)
type var = {
  index : var_id;  (** Unique index identifying the variable *)
  name : string option;
      (** Variable name - may be `None` if the variable was introduced by Rust
        through desugaring.
     *)
  var_ty : ty;  (** The variable type *)
}

and fun_decl_id = FunDeclId.id

(** The id of a translated item. *)
and any_decl_id =
  | IdType of type_decl_id
  | IdFun of fun_decl_id
  | IdGlobal of global_decl_id
  | IdTraitDecl of trait_decl_id
  | IdTraitImpl of trait_impl_id
[@@deriving show, ord]

(* Ancestors for the statement_base visitors *)
class ['self] iter_statement_base_base =
  object (self : 'self)
    inherit [_] iter_rvalue
    method visit_abort_kind : 'env -> abort_kind -> unit = fun _ _ -> ()
  end

class ['self] map_statement_base_base =
  object (self : 'self)
    inherit [_] map_rvalue
    method visit_abort_kind : 'env -> abort_kind -> abort_kind = fun _ x -> x
  end

(** A function operand is used in function calls.
    It either designates a top-level function, or a place in case
    we are using function pointers stored in local variables.
 *)
type fn_operand =
  | FnOpRegular of fn_ptr
      (** Regular case: call to a top-level function, trait method, etc. *)
  | FnOpMove of place
      (** Use of a function pointer stored in a local variable *)

and call = { func : fn_operand; args : operand list; dest : place }

(** Asserts are special constructs introduced by Rust to perform dynamic
    checks, to detect out-of-bounds accesses or divisions by zero for
    instance. We eliminate the assertions in [crate::remove_dynamic_checks],
    then introduce other dynamic checks in [crate::reconstruct_asserts].
 *)
and assertion = { cond : operand; expected : bool }
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_statement_base";
        variety = "iter";
        ancestors = [ "iter_statement_base_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_statement_base";
        variety = "map";
        ancestors = [ "map_statement_base_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

(** The local variables of a body. *)
type locals = {
  arg_count : int;
      (** The number of local variables used for the input arguments. *)
  vars : var list;
      (** The local variables.
        We always have, in the following order:
        - the local used for the return value (index 0)
        - the `arg_count` input arguments
        - the remaining locals, used for the intermediate computations
     *)
}

(** An expression body.
    TODO: arg_count should be stored in GFunDecl below. But then,
          the print is obfuscated and Aeneas may need some refactoring.
 *)
and 'a0 gexpr_body = {
  span : span;
  locals : locals;  (** The local variables. *)
  body : 'a0;
}

(** Item kind: whether this function/const is part of a trait declaration, trait implementation, or
    neither.

    Example:
    ```text
    trait Foo {
        fn bar(x : u32) -> u32; // trait item decl without default

        fn baz(x : bool) -> bool { x } // trait item decl with default
    }

    impl Foo for ... {
        fn bar(x : u32) -> u32 { x } // trait item implementation
    }

    fn test(...) { ... } // regular

    impl Type {
        fn test(...) { ... } // regular
    }
    ```
 *)
and item_kind =
  | RegularItem
      (** A function/const at the top level or in an inherent impl block. *)
  | TraitDeclItem of trait_decl_id * trait_item_name * bool
      (** Function/const that is part of a trait declaration. It has a body if and only if the trait
          provided a default implementation.

          Fields:
          - [trait_id]:  The trait declaration this item belongs to.
          - [item_name]:  The name of the item.
          - [has_default]:  Whether the trait declaration provides a default implementation.
       *)
  | TraitImplItem of trait_impl_id * trait_decl_id * trait_item_name * bool
      (** Function/const that is part of a trait implementation.

          Fields:
          - [impl_id]:  The trait implementation the method belongs to
          - [trait_id]:  The trait declaration this item belongs to.
          - [item_name]:  The name of the item
          - [reuses_default]:  True if the trait decl had a default implementation for this function/const and this
          item is a copy of the default item.
       *)

(** A global variable definition (constant or static). *)
and global_decl = {
  def_id : global_decl_id;
  item_meta : item_meta;  (** The meta data associated with the declaration. *)
  generics : generic_params;
  ty : ty;
  kind : item_kind;
      (** The global kind: "regular" function, trait const declaration, etc. *)
  body : fun_decl_id;
      (** The initializer function used to compute the initial value for this constant/static. *)
}

(** A trait **declaration**.

    For instance:
    ```text
    trait Foo {
      type Bar;

      fn baz(...); // required method (see below)

      fn test() -> bool { true } // provided method (see below)
    }
    ```

    In case of a trait declaration, we don't include the provided methods (the methods
    with a default implementation): they will be translated on a per-need basis. This is
    important for two reasons:
    - this makes the trait definitions a lot smaller (the Iterator trait
      has *one* declared function and more than 70 provided functions)
    - this is important for the external traits, whose provided methods
      often use features we don't support yet

    Remark:
    In Aeneas, we still translate the provided methods on an individual basis,
    and in such a way thay they take as input a trait instance. This means that
    we can use default methods *but*:
    - implementations of required methods shoudln't call default methods
    - trait implementations shouldn't redefine required methods
    The use case we have in mind is [std::iter::Iterator]: it declares one required
    method (`next`) that should be implemented for every iterator, and defines many
    helpers like `all`, `map`, etc. that shouldn't be re-implemented.
    Of course, this forbids other useful use cases such as visitors implemented
    by means of traits.
 *)
and trait_decl = {
  def_id : trait_decl_id;
  item_meta : item_meta;
  generics : generic_params;
  parent_clauses : trait_clause list;
      (** The "parent" clauses: the supertraits.

        Supertraits are actually regular where clauses, but we decided to have
        a custom treatment.
        ```text
        trait Foo : Bar {
                    ^^^
                supertrait, that we treat as a parent predicate
        }
        ```
        TODO: actually, as of today, we consider that all trait clauses of
        trait declarations are parent clauses.
     *)
  consts : (trait_item_name * ty) list;
      (** The associated constants declared in the trait, along with their type. *)
  types : trait_item_name list;
      (** The associated types declared in the trait. *)
  required_methods : (trait_item_name * fun_decl_id) list;
      (** The *required* methods.

        The required methods are the methods declared by the trait but with no default
        implementation. The corresponding `FunDecl`s don't have a body.
     *)
  provided_methods : (trait_item_name * fun_decl_id) list;
      (** The *provided* methods.

        The provided methods are the methods with a default implementation. The corresponding
        `FunDecl`s may have a body, according to the usual rules for extracting function bodies.
     *)
}

(** A trait **implementation**.

    For instance:
    ```text
    impl Foo for List {
      type Bar = ...

      fn baz(...) { ... }
    }
    ```
 *)
and trait_impl = {
  def_id : trait_impl_id;
  item_meta : item_meta;
  impl_trait : trait_decl_ref;
      (** The information about the implemented trait.
        Note that this contains the instantiation of the "parent"
        clauses.
     *)
  generics : generic_params;
  parent_trait_refs : trait_ref list;
      (** The trait references for the parent clauses (see [TraitDecl]). *)
  consts : (trait_item_name * global_decl_ref) list;
      (** The associated constants declared in the trait. *)
  types : (trait_item_name * ty) list;
      (** The associated types declared in the trait. *)
  required_methods : (trait_item_name * fun_decl_id) list;
      (** The implemented required methods *)
  provided_methods : (trait_item_name * fun_decl_id) list;
      (** The re-implemented provided methods *)
}

(** We use this to store information about the parameters in parent blocks.
    This is necessary because in the definitions we store *all* the generics,
    including those coming from the outer impl block.

    For instance:
    ```text
    impl Foo<T> {
            ^^^
          outer block generics
      fn bar<U>(...)  { ... }
            ^^^
          generics local to the function bar
    }
    ```

    In `bar` we store the generics: `[T, U]`.

    We however sometimes need to make a distinction between those two kinds
    of generics, in particular when manipulating traits. For instance:

    ```text
    impl<T> Foo for Bar<T> {
      fn baz<U>(...)  { ... }
    }

    fn test(...) {
       x.baz(...); // Here, we refer to the call as:
                   // > Foo<T>::baz<U>(...)
                   // If baz hadn't been a method implementation of a trait,
                   // we would have refered to it as:
                   // > baz<T, U>(...)
                   // The reason is that with traits, we refer to the whole
                   // trait implementation (as if it were a structure), then
                   // pick a specific method inside (as if projecting a field
                   // from a structure).
    }
    ```

    **Remark**: Rust only allows refering to the generics of the immediately
    outer block. For this reason, when we need to store the information about
    the generics of the outer block(s), we need to do it only for one level
    (this definitely makes things simpler).
 *)
and params_info = {
  num_region_params : int;
  num_type_params : int;
  num_const_generic_params : int;
  num_trait_clauses : int;
  num_regions_outlive : int;
  num_types_outlive : int;
  num_trait_type_constraints : int;
}

and closure_kind = Fn | FnMut | FnOnce

(** Additional information for closures.
    We mostly use it in micro-passes like [crate::update_closure_signature].
 *)
and closure_info = {
  kind : closure_kind;
  state : ty list;
      (** Contains the types of the fields in the closure state.
        More precisely, for every place captured by the
        closure, the state has one field (typically a ref).

        For instance, below the closure has a state with two fields of type `&u32`:
        ```text
        pub fn test_closure_capture(x: u32, y: u32) -> u32 {
          let f = &|z| x + y + z;
          (f)(0)
        }
        ```
     *)
}

(** A function signature. *)
and fun_sig = {
  is_unsafe : bool;  (** Is the function unsafe or not *)
  is_closure : bool;
      (** `true` if the signature is for a closure.

        Importantly: if the signature is for a closure, then:
        - the type and const generic params actually come from the parent function
          (the function in which the closure is defined)
        - the region variables are local to the closure
     *)
  closure_info : closure_info option;
      (** Additional information if this is the signature of a closure. *)
  generics : generic_params;
  parent_params_info : params_info option;
      (** Optional fields, for trait methods only (see the comments in [ParamsInfo]). *)
  inputs : ty list;
  output : ty;
}

(** A (group of) top-level declaration(s), properly reordered. *)
and declaration_group =
  | TypeGroup of type_decl_id g_declaration_group
      (** A type declaration group *)
  | FunGroup of fun_decl_id g_declaration_group
      (** A function declaration group *)
  | GlobalGroup of global_decl_id g_declaration_group
      (** A global declaration group *)
  | TraitDeclGroup of trait_decl_id g_declaration_group
  | TraitImplGroup of trait_impl_id g_declaration_group
  | MixedGroup of any_decl_id g_declaration_group
      (** Anything that doesn't fit into these categories. *)

(** A (group of) top-level declaration(s), properly reordered.
    "G" stands for "generic"
 *)
and 'a0 g_declaration_group =
  | NonRecGroup of 'a0  (** A non-recursive declaration *)
  | RecGroup of 'a0 list  (** A (group of mutually) recursive declaration(s) *)
[@@deriving show]

(* Hand-written because they don't exist in rust *)
type type_declaration_group = TypeDeclId.id g_declaration_group
[@@deriving show]

type fun_declaration_group = FunDeclId.id g_declaration_group [@@deriving show]

type global_declaration_group = GlobalDeclId.id g_declaration_group
[@@deriving show]

type trait_declaration_group = TraitDeclId.id g_declaration_group
[@@deriving show]

type trait_impl_group = TraitImplId.id g_declaration_group [@@deriving show]
type mixed_declaration_group = any_decl_id g_declaration_group [@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)
type 'body gfun_decl = {
  def_id : FunDeclId.id;
  item_meta : item_meta;
  signature : fun_sig;
  kind : item_kind;
  body : 'body gexpr_body option;
  is_global_decl_body : bool;
}
[@@deriving show]

(* Hand-written because the rust equivalent isn't generic *)

(** A crate *)
type 'fun_body gcrate = {
  name : string;
  declarations : declaration_group list;
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : 'fun_body gfun_decl FunDeclId.Map.t;
  global_decls : global_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
  source_files : string FileNameMap.t;
}
[@@deriving show]
