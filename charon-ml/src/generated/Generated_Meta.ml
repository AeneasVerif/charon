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

let hash_path_buf = HashBasic.hash_string

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
  | RustcAttributeKindExportName of string * span
      (** Represents
          [[#[export_name]]](https://doc.rust-lang.org/reference/abi.html#the-export_name-attribute).

          Fields:
          - [name]: The name to export this item with. It may not contain \0
            bytes as it will be converted to a null-terminated string.
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
  | RustcAttributeKindLinkSection of string
      (** Represents
          [[#[link_section]]](https://doc.rust-lang.org/reference/abi.html#the-link_section-attribute)

          Fields:
          - [name] *)
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

let rec hash_assoc_const_id : assoc_const_id -> int =
 fun (x : assoc_const_id) -> AssocConstId.hash_id x

and hash_assoc_item_id : assoc_item_id -> int =
 fun (x : assoc_item_id) ->
  match x with
  | AssocIdType x0 -> HashBasic.combine 0 (hash_assoc_type_id x0)
  | AssocIdMethod x0 -> HashBasic.combine 1 (hash_trait_method_id x0)
  | AssocIdConst x0 -> HashBasic.combine 2 (hash_assoc_const_id x0)

and hash_assoc_type_id : assoc_type_id -> int =
 fun (x : assoc_type_id) -> AssocTypeId.hash_id x

and hash_attr_info : attr_info -> int =
 fun (x : attr_info) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine 0
             ((HashBasic.hash_list hash_attribute) x.attributes))
          ((HashBasic.hash_option hash_inline_attr) x.inline))
       ((HashBasic.hash_option HashBasic.hash_string) x.rename))
    (HashBasic.hash_bool x.public)

and hash_attribute : attribute -> int =
 fun (x : attribute) ->
  match x with
  | AttrOpaque -> 0
  | AttrExclude -> 1
  | AttrRename x0 -> HashBasic.combine 2 (HashBasic.hash_string x0)
  | AttrVariantsPrefix x0 -> HashBasic.combine 3 (HashBasic.hash_string x0)
  | AttrVariantsSuffix x0 -> HashBasic.combine 4 (HashBasic.hash_string x0)
  | AttrTransparent -> 5
  | AttrIsContract (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 6 (HashBasic.hash_string x0))
        (hash_maybe_assoc_item_id x1)
  | AttrHasContract (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 7 (HashBasic.hash_string x0))
        (hash_fun_decl_id x1)
  | AttrDocComment x0 -> HashBasic.combine 8 (HashBasic.hash_string x0)
  | AttrBuiltin x0 -> HashBasic.combine 9 (hash_rustc_attribute_kind x0)
  | AttrUnknown x0 -> HashBasic.combine 10 (hash_raw_attribute x0)

and hash_rustc_attribute_kind : rustc_attribute_kind -> int =
 fun (x : rustc_attribute_kind) ->
  match x with
  | RustcAttributeKindAutomaticallyDerived -> 0
  | RustcAttributeKindCold -> 1
  | RustcAttributeKindDeprecated (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 2 (hash_rustc_deprecation x0))
        (hash_span x1)
  | RustcAttributeKindExportName (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 3 (HashBasic.hash_string x0))
        (hash_span x1)
  | RustcAttributeKindFundamental -> 4
  | RustcAttributeKindIgnore (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 5 (hash_span x0))
        ((HashBasic.hash_option HashBasic.hash_string) x1)
  | RustcAttributeKindInline (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 6 (hash_rustc_inline_attr x0))
        (hash_span x1)
  | RustcAttributeKindLinkSection x0 ->
      HashBasic.combine 7 (HashBasic.hash_string x0)
  | RustcAttributeKindMayDangle x0 -> HashBasic.combine 8 (hash_span x0)
  | RustcAttributeKindNaked x0 -> HashBasic.combine 9 (hash_span x0)
  | RustcAttributeKindNoLink -> 10
  | RustcAttributeKindNoMangle x0 -> HashBasic.combine 11 (hash_span x0)
  | RustcAttributeKindNonExhaustive x0 -> HashBasic.combine 12 (hash_span x0)
  | RustcAttributeKindOptimize (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 13 (hash_rustc_optimize_attr x0))
        (hash_span x1)
  | RustcAttributeKindRustcAlign (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 14 (HashBasic.hash_int x0))
        (hash_span x1)
  | RustcAttributeKindRustcIntrinsic -> 15
  | RustcAttributeKindShouldPanic x0 ->
      HashBasic.combine 16 ((HashBasic.hash_option HashBasic.hash_string) x0)
  | RustcAttributeKindTargetFeature (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 17
              ((HashBasic.hash_list (fun (x0, x1) ->
                    HashBasic.combine
                      (HashBasic.combine 0 (HashBasic.hash_string x0))
                      (hash_span x1)))
                 x0))
           (hash_span x1))
        (HashBasic.hash_bool x2)
  | RustcAttributeKindTrackCaller x0 -> HashBasic.combine 18 (hash_span x0)

and hash_rustc_deprecated_since : rustc_deprecated_since -> int =
 fun (x : rustc_deprecated_since) ->
  match x with
  | RustcDeprecatedSinceRustcVersion x0 ->
      HashBasic.combine 0 (hash_rustc_rustc_version x0)
  | RustcDeprecatedSinceFuture -> 1
  | RustcDeprecatedSinceNonStandard x0 ->
      HashBasic.combine 2 (HashBasic.hash_string x0)
  | RustcDeprecatedSinceUnspecified -> 3
  | RustcDeprecatedSinceErr -> 4

and hash_rustc_deprecation : rustc_deprecation -> int =
 fun (x : rustc_deprecation) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_rustc_deprecated_since x.since))
       ((HashBasic.hash_option hash_rustc_ident) x.note))
    ((HashBasic.hash_option HashBasic.hash_string) x.suggestion)

and hash_file : file -> int =
 fun (x : file) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_file_name x.name))
       (HashBasic.hash_string x.crate_name))
    ((HashBasic.hash_option HashBasic.hash_string) x.contents)

and hash_file_id : file_id -> int = fun (x : file_id) -> hash_file x

and hash_file_name : file_name -> int =
 fun (x : file_name) ->
  match x with
  | Virtual x0 -> HashBasic.combine 0 (hash_path_buf x0)
  | Local x0 -> HashBasic.combine 1 (hash_path_buf x0)
  | NotReal x0 -> HashBasic.combine 2 (HashBasic.hash_string x0)

and hash_fun_decl_id : fun_decl_id -> int =
 fun (x : fun_decl_id) -> FunDeclId.hash_id x

and hash_global_decl_id : global_decl_id -> int =
 fun (x : global_decl_id) -> GlobalDeclId.hash_id x

and hash_rustc_ident : rustc_ident -> int =
 fun (x : rustc_ident) ->
  HashBasic.combine
    (HashBasic.combine 0 (HashBasic.hash_string x.name))
    (hash_span x.span)

and hash_inline_attr : inline_attr -> int =
 fun (x : inline_attr) ->
  match x with
  | Hint -> 0
  | Never -> 1
  | Always -> 2

and hash_rustc_inline_attr : rustc_inline_attr -> int =
 fun (x : rustc_inline_attr) ->
  match x with
  | RustcInlineAttrNone -> 0
  | RustcInlineAttrHint -> 1
  | RustcInlineAttrAlways -> 2
  | RustcInlineAttrNever -> 3
  | RustcInlineAttrForce (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 4 (hash_span x0))
        ((HashBasic.hash_option HashBasic.hash_string) x1)

and hash_item_id : item_id -> int =
 fun (x : item_id) ->
  match x with
  | IdType x0 -> HashBasic.combine 0 (hash_type_decl_id x0)
  | IdTraitDecl x0 -> HashBasic.combine 1 (hash_trait_decl_id x0)
  | IdTraitImpl x0 -> HashBasic.combine 2 (hash_trait_impl_id x0)
  | IdFun x0 -> HashBasic.combine 3 (hash_fun_decl_id x0)
  | IdGlobal x0 -> HashBasic.combine 4 (hash_global_decl_id x0)

and hash_loc : loc -> int =
 fun (x : loc) ->
  HashBasic.combine
    (HashBasic.combine 0 (HashBasic.hash_int x.line))
    (HashBasic.hash_int x.col)

and hash_maybe_assoc_item_id : maybe_assoc_item_id -> int =
 fun (x : maybe_assoc_item_id) ->
  match x with
  | ItemFree x0 -> HashBasic.combine 0 (hash_item_id x0)
  | ItemAssoc (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 1 (hash_trait_decl_id x0))
        (hash_assoc_item_id x1)

and hash_rustc_optimize_attr : rustc_optimize_attr -> int =
 fun (x : rustc_optimize_attr) ->
  match x with
  | RustcOptimizeAttrDefault -> 0
  | RustcOptimizeAttrDoNotOptimize -> 1
  | RustcOptimizeAttrSpeed -> 2
  | RustcOptimizeAttrSize -> 3

and hash_raw_attribute : raw_attribute -> int =
 fun (x : raw_attribute) ->
  HashBasic.combine
    (HashBasic.combine 0 (HashBasic.hash_string x.path))
    ((HashBasic.hash_option HashBasic.hash_string) x.args)

and hash_rustc_rustc_version : rustc_rustc_version -> int =
 fun (x : rustc_rustc_version) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (HashBasic.hash_int x.major))
       (HashBasic.hash_int x.minor))
    (HashBasic.hash_int x.patch)

and hash_span : span -> int =
 fun (x : span) ->
  HashBasic.combine
    (HashBasic.combine 0 (hash_span_data x.data))
    ((HashBasic.hash_option hash_span_data) x.generated_from_span)

and hash_span_data : span_data -> int =
 fun (x : span_data) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_file_id x.file))
       (hash_loc x.beg_loc))
    (hash_loc x.end_loc)

and hash_trait_decl_id : trait_decl_id -> int =
 fun (x : trait_decl_id) -> TraitDeclId.hash_id x

and hash_trait_impl_id : trait_impl_id -> int =
 fun (x : trait_impl_id) -> TraitImplId.hash_id x

and hash_trait_method_id : trait_method_id -> int =
 fun (x : trait_method_id) -> TraitMethodId.hash_id x

and hash_type_decl_id : type_decl_id -> int =
 fun (x : type_decl_id) -> TypeDeclId.hash_id x
