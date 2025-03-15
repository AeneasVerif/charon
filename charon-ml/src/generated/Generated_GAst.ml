(** WARNING: this file is partially auto-generated. Do not edit `GAst.ml`
    by hand. Edit `GAst.template.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `GAst.template.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

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

type fun_decl_id = Types.fun_decl_id [@@deriving show, ord]

(** A variable *)
type var = {
  index : var_id;  (** Unique index identifying the variable *)
  name : string option;
      (** Variable name - may be `None` if the variable was introduced by Rust
        through desugaring.
     *)
  var_ty : ty;  (** The variable type *)
}

(** The local variables of a body. *)
and locals = {
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
  | TraitDeclItem of trait_decl_ref * trait_item_name * bool
      (** Function/const that is part of a trait declaration. It has a body if and only if the trait
          provided a default implementation.

          Fields:
          - [trait_ref]:  The trait declaration this item belongs to.
          - [item_name]:  The name of the item.
          - [has_default]:  Whether the trait declaration provides a default implementation.
       *)
  | TraitImplItem of trait_impl_ref * trait_decl_ref * trait_item_name * bool
      (** Function/const that is part of a trait implementation.

          Fields:
          - [impl_ref]:  The trait implementation the method belongs to.
          - [trait_ref]:  The trait declaration that the impl block implements.
          - [item_name]:  The name of the item
          - [reuses_default]:  True if the trait decl had a default implementation for this function/const and this
          item is a copy of the default item.
       *)

(** A function operand is used in function calls.
    It either designates a top-level function, or a place in case
    we are using function pointers stored in local variables.
 *)
and fn_operand =
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
  inputs : ty list;
  output : ty;
}
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
  kind : item_kind;
      (** The global kind: "regular" function, trait const declaration, etc. *)
  body : fun_decl_id;
      (** The initializer function used to compute the initial value for this constant/static. It
        uses the same generic parameters as the global.
     *)
}
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
type trait_decl = {
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
  methods : (trait_item_name * fun_decl_ref binder) list;
      (** The methods declared by the trait. The signature of the methods can be found in each
        corresponding `FunDecl`. These `FunDecl` may have a body if the trait provided a default
        implementation for that method; otherwise it has an `Opaque` body.

        The binder contains the type parameters specific to the method. The `FunDeclRef` then
        provides a full list of arguments to the pointed-to function.
     *)
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
        ancestors = [ "iter_global_decl" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_trait_decl";
        monomorphic = [ "env" ];
        variety = "map";
        ancestors = [ "map_global_decl" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

(** A trait **implementation**.

    For instance:
    ```text
    impl Foo for List {
      type Bar = ...

      fn baz(...) { ... }
    }
    ```
 *)
type trait_impl = {
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
  methods : (trait_item_name * fun_decl_ref binder) list;
      (** The implemented methods *)
}
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

(** An expression body.
    TODO: arg_count should be stored in GFunDecl below. But then,
          the print is obfuscated and Aeneas may need some refactoring.
 *)
type 'a0 gexpr_body = {
  span : span;
  locals : locals;  (** The local variables. *)
  body : 'a0;
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

and cli_options = {
  ullbc : bool;
      (** Extract the unstructured LLBC (i.e., don't reconstruct the control-flow) *)
  lib : bool;  (** Compile the package's library *)
  bin : string option;  (** Compile the specified binary *)
  mir_promoted : bool;  (** Extract the promoted MIR instead of the built MIR *)
  mir_optimized : bool;
      (** Extract the optimized MIR instead of the built MIR *)
  crate_name : string option;
      (** Provide a custom name for the compiled crate (ignore the name computed
        by Cargo)
     *)
  input_file : path_buf option;
      (** The input file (the entry point of the crate to extract).
        This is needed if you want to define a custom entry point (to only
        extract part of a crate for instance).
     *)
  read_llbc : path_buf option;
      (** Read an llbc file and pretty-print it. This is a terrible API, we should use subcommands. *)
  dest_dir : path_buf option;
      (** The destination directory. Files will be generated as `<dest_dir>/<crate_name>.{u}llbc`,
        unless `dest_file` is set. `dest_dir` defaults to the current directory.
     *)
  dest_file : path_buf option;
      (** The destination file. By default `<dest_dir>/<crate_name>.llbc`. If this is set we ignore
        `dest_dir`.
     *)
  use_polonius : bool;
      (** If activated, use Polonius' non-lexical lifetimes (NLL) analysis.
        Otherwise, use the standard borrow checker.
     *)
  skip_borrowck : bool;
      (** If activated, this skips borrow-checking of the crate. *)
  no_code_duplication : bool;
  monomorphize : bool;
      (** Monomorphize the code, replacing generics with their concrete types. *)
  extract_opaque_bodies : bool;
      (** Usually we skip the bodies of foreign methods and structs with private fields. When this
        flag is on, we don't.
     *)
  translate_all_methods : bool;
      (** Usually we skip the provided methods that aren't used. When this flag is on, we translate
        them all.
     *)
  included : string list;
      (** Whitelist of items to translate. These use the name-matcher syntax. *)
  opaque : string list;
      (** Blacklist of items to keep opaque. These use the name-matcher syntax. *)
  exclude : string list;
      (** Blacklist of items to not translate at all. These use the name-matcher syntax. *)
  remove_associated_types : string list;
      (** List of traits for which we transform associated types to type parameters. *)
  hide_marker_traits : bool;
      (** Whether to hide the `Sized`, `Sync`, `Send` and `Unpin` marker traits anywhere they show
        up.
     *)
  no_cargo : bool;  (** Do not run cargo; instead, run the driver directly. *)
  rustc_args : string list;  (** Extra flags to pass to rustc. *)
  cargo_args : string list;
      (** Extra flags to pass to cargo. Incompatible with `--no-cargo`. *)
  only_cargo : bool;
      (** Do nothing! Just run cargo, don't do any translation. *)
  abort_on_error : bool;
      (** Panic on the first error. This is useful for debugging. *)
  error_on_warnings : bool;  (** Print the errors as warnings *)
  no_serialize : bool;
  print_original_ullbc : bool;
  print_ullbc : bool;
  print_built_llbc : bool;
  print_llbc : bool;
  no_merge_goto_chains : bool;
}

(** A (group of) top-level declaration(s), properly reordered.
    "G" stands for "generic"
 *)
and 'a0 g_declaration_group =
  | NonRecGroup of 'a0  (** A non-recursive declaration *)
  | RecGroup of 'a0 list  (** A (group of mutually) recursive declaration(s) *)
[@@deriving show]
