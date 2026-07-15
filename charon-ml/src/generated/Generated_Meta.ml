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

(** Information about the attributes and visibility of an item, field or
    variant.. *)
type attr_info = {
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
  | AttrIsPrecondition of item_id
      (** An item annotated with [#[charon::precondition]]. This makes it a
          precondition for its parent item. *)
  | AttrIsPostcondition of item_id
      (** An item annotated with [#[charon::postcondition]]. This makes it a
          postcondition for its parent item. *)
  | AttrHasPrecondition of fun_decl_id
      (** An item that has a precondition that applies to it. The referenced
          item is a function the specifies the condition. *)
  | AttrHasPostcondition of fun_decl_id
      (** An item that has a postcondition that applies to it. The referenced
          item is a function the specifies the condition. *)
  | AttrDocComment of string  (** A doc-comment such as [/// ...]. *)
  | AttrUnknown of raw_attribute  (** A non-charon-specific attribute. *)

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

(** [#[inline]] built-in attribute. *)
and inline_attr =
  | Hint  (** [#[inline]] *)
  | Never  (** [#[inline(never)]] *)
  | Always  (** [#[inline(always)]] *)

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

(** A general attribute. *)
and raw_attribute = {
  path : string;
  args : string option;
      (** The arguments passed to the attribute, if any. We don't distinguish
          different delimiters or the [path = lit] case. *)
}

(** Meta information about a piece of code (block, statement, etc.) *)
and span = {
  data : span_data;
      (** The source code span.

          If this meta information is for a statement/terminator coming from a
          macro expansion/inlining/etc., this span is (in case of macros) for
          the macro before expansion (i.e., the location the code where the user
          wrote the call to the macro).

          Ex:
          {@rust[
            // Below, we consider the spans for the statements inside [test]

            //   the statement we consider, which gets inlined in [test]
                                     VV
            macro_rules! macro { ... st ... } // [generated_from_span] refers to this location

            fn test() {
                macro!(); // <-- [span] refers to this location
            }
          ]} *)
  generated_from_span : span_data option;
      (** Where the code actually comes from, in case of macro
          expansion/inlining/etc. *)
}

(** Span information *)
and span_data = { file : file_id; beg_loc : loc; end_loc : loc }

and trait_decl_id = (TraitDeclId.id[@visitors.opaque])
and trait_impl_id = (TraitImplId.id[@visitors.opaque])

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
