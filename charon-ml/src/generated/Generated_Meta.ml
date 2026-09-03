(** WARNING: this file is partially auto-generated. Do not edit `src/Meta.ml` by
    hand. Edit `generate_ml/templates/Meta.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/Meta.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`. *)

open Identifiers
module TypeDeclId = IdGen ()
module GlobalDeclId = IdGen ()
module TraitDeclId = IdGen ()
module TraitImplId = IdGen ()
module FunDeclId = IdGen ()
module TraitMethodId = IdGen ()
module AssocTypeId = IdGen ()
module AssocConstId = IdGen ()

type path_buf = string [@@deriving show, ord, eq]

(* Ancestors for the meta visitors *)
class ['self] iter_meta_base =
  object (self : 'self)
    inherit [_] BigInt.iter_big_int
    method visit_path_buf : 'env -> path_buf -> unit = fun _ _ -> ()
  end

class ['self] map_meta_base =
  object (self : 'self)
    inherit [_] BigInt.map_big_int
    method visit_path_buf : 'env -> path_buf -> path_buf = fun _ x -> x
  end

class virtual ['self] reduce_meta_base =
  object (self : 'self)
    inherit [_] BigInt.reduce_big_int
    method visit_path_buf : 'env -> path_buf -> 'a = fun _ _ -> self#zero
  end

class virtual ['self] mapreduce_meta_base =
  object (self : 'self)
    inherit [_] BigInt.mapreduce_big_int

    method visit_path_buf : 'env -> path_buf -> path_buf * 'a =
      fun _ x -> (x, self#zero)
  end

type assoc_const_id = (AssocConstId.id[@visitors.opaque])

(** The id of an associated item within a trait. *)
and assoc_item_id =
  | AssocIdType of assoc_type_id
  | AssocIdMethod of trait_method_id
  | AssocIdConst of assoc_const_id

and assoc_type_id = (AssocTypeId.id[@visitors.opaque])

(** Information about the attributes and visibility of an item, field or
    variant.. *)
and attr_info = {
  attributes : attribute list;  (** Attributes ([#[...]]). *)
  inline : inline_attr option;  (** Inline hints (on functions only). *)
  rename : string option;
      (** The name computed from [charon::rename] and [charon::variants_prefix]
          attributes, if any. This provides a custom name that can be used by
          consumers of llbc. E.g. Aeneas uses this to rename definitions in the
          extracted code. *)
  public : bool;
      (** Whether this item is declared public. Impl blocks and closures don't
          have visibility modifiers; we arbitrarily set this to [false] for
          them.

          Note that this is different from being part of the crate's public API:
          to be part of the public API, an item has to also be reachable from
          public items in the crate root. For example:
          {@rust[
            mod foo {
                pub struct X;
            }
            mod bar {
                pub fn something(_x: super::foo::X) {}
            }
            pub use bar::something; // exposes [X]
          ]}
          Without the [pub use ...], neither [X] nor [something] would be part
          of the crate's public API (this is called "pub-in-priv" items). With
          or without the [pub use], we set [public = true]; computing item
          reachability is harder. *)
}

(** Attributes ([#[...]]). *)
and attribute =
  | AttrOpaque
      (** Do not translate the body of this item. Written [#[charon::opaque]] *)
  | AttrExclude
      (** Do not translate this item at all. Written [#[charon::exclude]] *)
  | AttrRename of string
      (** Provide a new name that consumers of the llbc can use. Written
          [#[charon::rename("new_name")]] *)
  | AttrVariantsPrefix of string
      (** For enums only: rename the variants by pre-pending their names with
          the given prefix. Written [#[charon::variants_prefix("prefix_")]]. *)
  | AttrVariantsSuffix of string
      (** Same as [VariantsPrefix], but appends to the name instead of
          pre-pending. *)
  | AttrTransparent
      (** The structure is treated as a transparent wrapper around its sole
          field. Written [#[charon::transparent]]. *)
  | AttrIsContract of string * maybe_assoc_item_id
      (** An item annotated with [#[charon::contract(kind = "...", parent)]] or
          [#[charon::contract(kind = "...", for = "...")]]. This makes it a
          contract for the target item.

          Fields:
          - [kind]
          - [target] *)
  | AttrHasContract of string * fun_decl_id
      (** An item that has a contract that applies to it. The referenced item is
          the function that specifies the contract.

          Fields:
          - [kind]
          - [contract] *)
  | AttrDocComment of string  (** A doc-comment such as [/// ...]. *)
  | AttrBuiltin of rustc_attribute_kind  (** A built-in attribute. *)
  | AttrUnknown of raw_attribute  (** None of the above. *)

(** Represents parsed *built-in* inert attributes.

    ## Overview These attributes are markers that guide the compilation process
    and are never expanded into other code. They persist throughout the
    compilation phases, from AST to HIR and beyond.

    ## Attribute Processing While attributes are initially parsed by
    [[rustc_parse]] into [[ast::Attribute]], they still contain raw token
    streams because different attributes have different internal structures.
    This enum represents the final, fully parsed form of these attributes, where
    each variant contains all the information and structure relevant for the
    specific attribute.

    Some attributes can be applied multiple times to the same item, and they are
    "collapsed" into a single semantic attribute. For example:
    {@rust[
      rust
      #[repr(C)]
      #[repr(packed)]
      struct S { }
    ]}
    This is equivalent to [#[repr(C, packed)]] and results in a single
    [[AttributeKind::Repr]] containing both [C] and [packed] annotations. This
    collapsing happens during parsing and is reflected in the data structures
    defined in this enum.

    ## Usage These parsed attributes are used throughout the compiler to:
    - Control code generation (e.g., [#[repr]])
    - Mark API stability ([#[stable]], [#[unstable]])
    - Provide documentation ([#[doc]])
    - Guide compiler behavior (e.g., [#[allow_internal_unstable]])

    ## Note on Attribute Organization Some attributes like [InlineAttr],
    [OptimizeAttr], and [InstructionSetAttr] are defined separately from this
    enum because they are used in specific compiler phases (like code
    generation) and don't need to persist throughout the entire compilation
    process. They are typically processed and converted into their final form
    earlier in the compilation pipeline.

    For example:
    - [InlineAttr] is used during code generation to control function inlining
    - [OptimizeAttr] is used to control optimization levels
    - [InstructionSetAttr] is used for target-specific code generation

    These attributes are handled by their respective compiler passes in the
    [[rustc_codegen_ssa]] crate and don't need to be preserved in the same way
    as the attributes in this enum.

    For more details on attribute parsing, see the [[rustc_attr_parsing]] crate.

    [[rustc_parse]]:
    https://doc.rust-lang.org/nightly/nightly-rustc/rustc_parse/index.html
    [[rustc_codegen_ssa]]:
    https://doc.rust-lang.org/nightly/nightly-rustc/rustc_codegen_ssa/index.html
    [[rustc_attr_parsing]]:
    https://doc.rust-lang.org/nightly/nightly-rustc/rustc_attr_parsing/index.html
*)
and rustc_attribute_kind =
  | RustcAttributeKindAutomaticallyDerived
      (** Represents [#[automatically_derived]] *)
  | RustcAttributeKindCold  (** Represents [#[cold]]. *)
  | RustcAttributeKindDeprecated of rustc_deprecation * span
      (** Represents
          [[#[deprecated]]](https://doc.rust-lang.org/stable/reference/attributes/diagnostics.html#the-deprecated-attribute).

          Fields:
          - [deprecation]
          - [span] *)
  | RustcAttributeKindFundamental  (** Represents [#[fundamental]]. *)
  | RustcAttributeKindIgnore of span * string option
      (** Represents [#[ignore]]

          Fields:
          - [span]
          - [reason]: ignore can optionally have a reason:
            [#[ignore = "reason this is ignored"]] *)
  | RustcAttributeKindInline of rustc_inline_attr * span
      (** Represents [#[inline]] and [#[rustc_force_inline]]. *)
  | RustcAttributeKindMayDangle of span
      (** Represents
          [[#[may_dangle]]](https://std-dev-guide.rust-lang.org/tricky/may-dangle.html).
      *)
  | RustcAttributeKindNaked of span  (** Represents [#[naked]] *)
  | RustcAttributeKindNoLink  (** Represents [#[no_link]] *)
  | RustcAttributeKindNoMangle of span  (** Represents [#[no_mangle]] *)
  | RustcAttributeKindNonExhaustive of span
      (** Represents [#[non_exhaustive]] *)
  | RustcAttributeKindOptimize of rustc_optimize_attr * span
      (** Represents [#[optimize(size|speed)]] *)
  | RustcAttributeKindRustcAlign of int * span
      (** Represents [#[align(N)]].

          Fields:
          - [align]
          - [span] *)
  | RustcAttributeKindRustcIntrinsic  (** Represents [#[rustc_intrinsic]] *)
  | RustcAttributeKindRustcTestEntrypointMarker
      (** Represents [#[rustc_test_entrypoint_marker]] *)
  | RustcAttributeKindShouldPanic of string option
      (** Represents [#[should_panic]]

          Fields:
          - [reason] *)
  | RustcAttributeKindTargetFeature of (string * span) list * span * bool
      (** Represents [#[target_feature(enable = "...")]] and
          [#[unsafe(force_target_feature(enable = "...")]].

          Fields:
          - [features]
          - [attr_span]
          - [was_forced] *)
  | RustcAttributeKindTrackCaller of span  (** Represents [#[track_caller]] *)

(** Release in which an API is deprecated. *)
and rustc_deprecated_since =
  | RustcDeprecatedSinceRustcVersion of rustc_rustc_version
  | RustcDeprecatedSinceFuture
      (** Deprecated in the future ("to be determined"). *)
  | RustcDeprecatedSinceNonStandard of string
      (** [feature(staged_api)] is off. Deprecation versions outside the
          standard library are allowed to be arbitrary strings, for better or
          worse. *)
  | RustcDeprecatedSinceUnspecified
      (** Deprecation version is unspecified but optional. *)
  | RustcDeprecatedSinceErr
      (** Failed to parse a deprecation version, or the deprecation version is
          unspecified and required. An error has already been emitted. *)

and rustc_deprecation = {
  since : rustc_deprecated_since;
  note : rustc_ident option;  (** The note to issue a reason. *)
  suggestion : string option;
      (** A text snippet used to completely replace any use of the deprecated
          item in an expression.

          This is currently unstable. *)
}

and file = {
  name : file_name;  (** The path to the file. *)
  crate_name : string;  (** Name of the crate this file comes from. *)
  contents : string option;
      (** The contents of the source file, as seen by rustc at the time of
          translation. Some files don't have contents. *)
}

and file_id = file

(** A filename. *)
and file_name =
  | Virtual of path_buf  (** A remapped path (namely paths into stdlib) *)
  | Local of path_buf
      (** A local path (a file coming from the current crate for instance) *)
  | NotReal of string  (** A "not real" file name (macro, query, etc.) *)

and fun_decl_id = (FunDeclId.id[@visitors.opaque])
and global_decl_id = (GlobalDeclId.id[@visitors.opaque])

and rustc_ident = {
  name : string;
      (** [name] should never be the empty symbol. If you are considering that,
          you are probably conflating "empty identifier with "no identifier" and
          you should use [Option<Ident>] instead. Trying to construct an [Ident]
          with an empty name will trigger debug assertions." *)
  span : span;
}

(** [#[inline]] built-in attribute. *)
and inline_attr =
  | Hint  (** [#[inline]] *)
  | Never  (** [#[inline(never)]] *)
  | Always  (** [#[inline(always)]] *)

and rustc_inline_attr =
  | RustcInlineAttrNone
  | RustcInlineAttrHint
  | RustcInlineAttrAlways
  | RustcInlineAttrNever
  | RustcInlineAttrForce of span * string option
      (** [#[rustc_force_inline]] forces inlining to happen in the MIR inliner -
          it reports an error if the inlining cannot happen. It is limited to
          only free functions so that the calls can always be resolved.

          Fields:
          - [attr_span]
          - [reason] *)

(** The id of a translated item. *)
and item_id =
  | IdType of type_decl_id
  | IdTraitDecl of trait_decl_id
  | IdTraitImpl of trait_impl_id
  | IdFun of fun_decl_id
  | IdGlobal of global_decl_id

and loc = {
  line : int;  (** The (1-based) line number. *)
  col : int;  (** The (0-based) column offset. *)
}

(** The id of a translated item or associated item definition. *)
and maybe_assoc_item_id =
  | ItemFree of item_id
  | ItemAssoc of trait_decl_id * assoc_item_id

and rustc_optimize_attr =
  | RustcOptimizeAttrDefault  (** No [#[optimize(..)]] attribute *)
  | RustcOptimizeAttrDoNotOptimize  (** [#[optimize(none)]] *)
  | RustcOptimizeAttrSpeed  (** [#[optimize(speed)]] *)
  | RustcOptimizeAttrSize  (** [#[optimize(size)]] *)

(** A general attribute. *)
and raw_attribute = {
  path : string;
  args : string option;
      (** The arguments passed to the attribute, if any. We don't distinguish
          different delimiters or the [path = lit] case. *)
}

and rustc_rustc_version = { major : int; minor : int; patch : int }

(** A snippet of source code within a file, along with the place the code was
    generated from in case of macro expansion. This is a pair of the span itself
    ([data]) and an optional "generated from" span ([generated_from_span]).

    For code coming from a macro expansion, [data] is the span of the macro
    before expansion, i.e. the location where the user wrote the call to the
    macro, and [generated_from_span] is where the code actually comes from.

    Ex:
    {@rust[
      // Below, we consider the spans for the statements inside [test]

      //   the statement we consider, which gets inlined in [test]
                               VV
      macro_rules! macro { ... st ... } // [generated_from_span] refers to this location

      fn test() {
          macro!(); // <-- [data] refers to this location
      }
    ]} *)
and span = {
  data : span_data;
      (** The source code span; for code coming from a macro expansion, the
          location of the macro call. *)
  generated_from_span : span_data option;
      (** Where the code actually comes from, in case of macro
          expansion/inlining/etc. *)
}

(** A snippet of source code within a file. *)
and span_data = { file : file_id; beg_loc : loc; end_loc : loc }

and trait_decl_id = (TraitDeclId.id[@visitors.opaque])
and trait_impl_id = (TraitImplId.id[@visitors.opaque])
and trait_method_id = (TraitMethodId.id[@visitors.opaque])

and type_decl_id = (TypeDeclId.id[@visitors.opaque])
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_meta";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_meta_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_meta";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_meta_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "reduce_meta";
      monomorphic = [ "env" ];
      variety = "reduce";
      ancestors = [ "reduce_meta_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "mapreduce_meta";
      monomorphic = [ "env" ];
      variety = "mapreduce";
      ancestors = [ "mapreduce_meta_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]
