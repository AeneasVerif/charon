(** WARNING: this file is partially auto-generated. Do not edit `FullAst.ml` by
    hand. Edit `templates/FullAst.ml` instead, or improve the code generation
    tool so avoid the need for hand-writing things.

    `templates/FullAst.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`. *)

open Generated_GAst
open Generated_UllbcAst
open Generated_LlbcAst
open Generated_Types
open Generated_Values
open Generated_Expressions
open Generated_Meta
open Identifiers

type assoc_item_names = {
  types : trait_item_name list;
  methods : trait_item_name list;
  consts : trait_item_name list;
}

(** The body of a function. *)
and body =
  | UnstructuredBody of Generated_UllbcAst.block list gexpr_body
      (** Body represented as a CFG. This is what ullbc is made of, and what we
          get after translating MIR. *)
  | StructuredBody of Generated_LlbcAst.block gexpr_body
      (** Body represented with structured control flow. This is what llbc is
          made of. We restructure the control flow in the [ullbc_to_llbc] pass.
      *)
  | TargetDispatchBody of (string * fun_decl_ref) list
      (** A façade body that dispatches to one of several per-target function
          bodies. Created during multi-target merging for functions with the
          same signature but different bodies across targets. *)
  | ExternBody of string
      (** Function declared in an [extern { ... }] block. The string is the
          foreign symbol name. *)
  | IntrinsicBody of string * string option list
      (** Rust intrinsic function.

          Fields:
          - [name]: The intrinsic name.
          - [arg_names]: The argument names, None if not available. *)
  | OpaqueBody
      (** A body that the user chose not to translate, based on opacity settings
          like [--include]/[--opaque]. *)
  | MissingBody
      (** A body that was not available. Typically that's function bodies for
          non-generic and non-inlineable std functions, as these are not present
          in the compiled standard library [.rmeta] file shipped with a rust
          toolchain. *)
  | ErrorBody of error
      (** We encountered an error while translating this body. *)

and cli_options = {
  ullbc : bool;
      (** Extract the unstructured LLBC (i.e., don't reconstruct the
          control-flow) *)
  precise_drops : bool;
      (** Whether to precisely translate drops and drop-related code. For this,
          we add explicit [Destruct] bounds to all generic parameters and set
          the MIR level to at least [elaborated].

          Without this option, drops may be "conditional" and we may lack
          information about what code is run on drop in a given polymorphic
          function body. *)
  skip_borrowck : bool;
      (** If activated, this skips borrow-checking of the crate. *)
  mir : mir_level option;
      (** The MIR stage to extract. This is only relevant for the current crate;
          for dependencies only MIR optimized is available. *)
  rustc_args : string list;  (** Extra flags to pass to rustc. *)
  targets : string list;
      (** A list of target architectures to translate for. Charon will run the
          compiler once for each target and aggregate the results, which is
          useful if the code includes [#[cfg(..)]] filters. Warning: this is an
          initial implementation which is extremely slow. *)
  sysroot : string option;
      (** Sysroot to use for rustc invocations. By default Charon builds a
          sysroot that has full MIR for the standard library. You can pass a
          custom sysroot to use instead, or pass "default" to use the normal
          distributed sysroot, which lacks MIR bodies for many standard library
          functions. *)
  monomorphize : bool;
      (** Monomorphize the items encountered when possible. Generic items found
          in the crate are skipped. To only translate a particular call graph,
          use [--start-from]. Note: this doesn't currently support [dyn Trait].
      *)
  monomorphize_mut : monomorphize_mut option;
      (** Partially monomorphize items to make it so that no item is ever
          monomorphized with a mutable reference (or type containing one); said
          differently, so that the presence of mutable references in a type is
          independent of its generics. This is used by Aeneas. *)
  start_from : string list;
      (** A list of item paths to use as starting points for the translation. We
          will translate these items and any items they refer to, according to
          the opacity rules. When absent, we start from the path [crate] (which
          translates the whole crate). *)
  start_from_if_exists : string list;
      (** Same as --start-from, but won't raise an error if a pattern doesn't
          match any item. This is useful when the patterns are generated by a
          build script and may be out of sync with the code. *)
  start_from_attribute : string list;
      (** Use all the items annotated with the given attribute(s) as starting
          points for translation (except modules). If an attribute name is not
          specified, [verify::start_from] is used. *)
  start_from_pub : bool;
      (** Use all the [pub] items as starting points for translation (except
          modules). *)
  included : string list;
      (** Whitelist of items to translate. These use the name-matcher syntax. *)
  opaque : string list;
      (** Blacklist of items to keep opaque. Works just like [--include], see
          the doc there. *)
  exclude : string list;
      (** Blacklist of items to not translate at all. Works just like
          [--include], see the doc there. *)
  extract_opaque_bodies : bool;
      (** Usually we skip the bodies of foreign methods and structs with private
          fields. When this flag is on, we don't. *)
  translate_all_methods : bool;
      (** Usually we skip the provided methods that aren't used. When this flag
          is on, we translate them all. *)
  duplicate_defaulted_methods : bool;
      (** Whenever an impl doesn't implement a method (because it has a default
          body), this creates a duplicate method as if it had been implemented.
          This can simplify the call-graphs as otherwise calls within the
          default body would be indirected through trait proofs. *)
  lift_associated_types : string list;
      (** Transform the associate types of traits to be type parameters instead.
          This takes a list of name patterns of the traits to transform, using
          the same syntax as [--include]. *)
  hide_marker_traits : bool;
      (** Whether to hide various marker traits such as [Sized], [Sync], and
          [Send] anywhere they show up. This can considerably speed up
          translation. *)
  hide_allocator : bool;
      (** Hide the [A] type parameter on standard library containers ([Box],
          [Vec], etc). *)
  remove_unused_clauses : bool;
      (** Remove trait clauses that aren't ultimately used anywhere. This is
          potentially incorrect as sometimes the mere presence of a trait clause
          is used to justify an operation, e.g. copying [Copy] data using
          [unsafe]. *)
  remove_unused_self_clauses : bool;
      (** Trait method default bodies take a [Self: Trait] clause as parameter,
          so that they can be reused by multiple trait impls. This however
          causes trait definitions to be mutually recursive with their default
          methods. This flag removes [Self] clauses that aren't used to break
          this mutual recursion when possible. *)
  remove_adt_clauses : bool;
      (** Remove trait clauses from type declarations. Best combined with
          [--lift-associated-types] for type declarations that use trait
          associated types in their fields. *)
  desugar_drops : bool;
      (** Transform precise drops to the equivalent [drop_glue(&mut p)] call. *)
  ops_to_function_calls : bool;
      (** Transform array-to-slice unsizing, repeat expressions, and raw pointer
          construction into builtin functions in ULLBC. *)
  index_to_function_calls : bool;
      (** Transform array/slice indexing into builtin functions in ULLBC. Note
          that this may introduce UB since it creates references that were not
          normally created, including when indexing behind a raw pointer. *)
  treat_box_as_builtin : bool;
      (** Treat [Box<T>] as if it was a built-in type. *)
  raw_consts : bool;  (** Do not inline or evaluate constants. *)
  consts : const_handling option;
      (** How to handle constants and statics: whether they should be
          represented as a call to their initializer function, or whether we
          should attempt to evaluate them into a value. When evaluation isn't
          possible (e.g. the constant is generic, or for recursive statics), we
          fall back to the initializer call. *)
  unsized_strings : bool;
      (** Replace string literal constants with a constant u8 array that gets
          unsized, expliciting the fact a string constant has a hidden
          reference. *)
  reconstruct_fallible_operations : bool;
      (** Replace "bound checks followed by UB-on-overflow operation" with the
          corresponding panic-on-overflow operation. This loses unwinding
          information. *)
  reconstruct_asserts : bool;
      (** Replace [if x { panic() }] with [assert(x)]. *)
  unbind_item_vars : bool;
      (** Use [DeBruijnVar::Free] for the variables bound in item signatures,
          instead of [DeBruijnVar::Bound] everywhere. This simplifies the
          management of generics for projects that don't intend to manipulate
          them too much. *)
  print_original_ullbc : bool;
      (** Pretty-print the ULLBC immediately after extraction from MIR. *)
  print_ullbc : bool;
      (** Pretty-print the ULLBC after applying the micro-passes (before
          serialization/control-flow reconstruction). *)
  print_built_llbc : bool;
      (** Pretty-print the LLBC just after we built it (i.e., immediately after
          loop reconstruction). *)
  print_llbc : bool;
      (** Pretty-print the final LLBC (after all the cleaning micro-passes). *)
  dest_dir : path_buf option;
      (** The destination directory. Files will be generated as
          [<dest_dir>/<crate_name>.{u}llbc] for json and
          [<dest_dir>/<crate_name>.{u}llbc.postcard] for postcard, unless
          [dest_file] is set. [dest_dir] defaults to the current directory. *)
  dest_file : path_buf option;
      (** The destination file. By default this depends on [format] and [ullbc].
          If this is set we ignore [dest_dir]. If used with [format=all], will
          add an extension corresponding to the file format at the end of the
          provided file name. *)
  no_dedup_serialized_ast : bool;
      (** Don't deduplicate values (types, trait refs) in the .(u)llbc file.
          This makes the file easier to inspect. *)
  format : serialization_format_arg option;
      (** Serialization format for emitted (U)LLBC files. Defaults to json. *)
  no_serialize : bool;  (** Don't serialize the final (U)LLBC to a file. *)
  no_typecheck : bool;  (** Skip the typecheck passes. *)
  no_normalize : bool;  (** Don't normalize associated types. *)
  no_reorder_decls : bool;
      (** Don't compute a stable order for declarations. *)
  abort_on_error : bool;
      (** Panic on the first error. This is useful for debugging. *)
  error_on_warnings : bool;  (** Consider any warnings to be errors. *)
  preset : preset option;  (** Named builtin sets of options. *)
}

(** How to handle constants and statics. *)
and const_handling =
  | Initializers
      (** Keep consts as calls to their initializer with
          [ConstantExprKind::Call], without attempting to do any
          const-evaluation. This is the default. *)
  | Values
      (** Try evaluating consts and statics to their final value. If evaluation
          fails, we fall back to the initializer call. *)

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
  | MixedGroup of item_id g_declaration_group
      (** Anything that doesn't fit into these categories. *)

(** A function definition *)
and fun_decl = {
  def_id : fun_decl_id;
  item_meta : item_meta;  (** The meta data associated with the declaration. *)
  generics : generic_params;
  signature : fun_sig;
      (** The signature contains the inputs/output types and ABI details. *)
  src : item_source;
      (** The function kind: "regular" function, trait method declaration, etc.
      *)
  is_global_initializer : global_decl_id option;
      (** Whether this function is in fact the body of a constant/static that we
          turned into an initializer function. *)
  body : body;  (** The function body. *)
}

(** A (group of) top-level declaration(s), properly reordered. "G" stands for
    "generic" *)
and 'a0 g_declaration_group =
  | NonRecGroup of 'a0  (** A non-recursive declaration *)
  | RecGroup of 'a0 list  (** A (group of mutually) recursive declaration(s) *)

(** The MIR stage to use. This is only relevant for the current crate: for
    dependencies, only mir optimized is available (or mir elaborated for
    consts). *)
and mir_level =
  | Built  (** The MIR just after MIR lowering. *)
  | Promoted
      (** The MIR after const promotion. This is the MIR used by the
          borrow-checker. *)
  | Elaborated
      (** The MIR after drop elaboration. This is the first MIR to include all
          the runtime information. *)
  | Optimized
      (** The MIR after optimizations. Charon disables all the optimizations it
          can, so this is sensibly the same MIR as the elaborated MIR. *)

and monomorphize_mut =
  | All  (** Monomorphize any item instantiated with [&mut]. *)
  | ExceptTypes
      (** Monomorphize all non-typedecl items instantiated with [&mut]. *)

(** Presets to make it easier to tweak options without breaking dependent
    projects. Eventually we should define semantically-meaningful presets
    instead of project-specific ones. *)
and preset =
  | OldDefaults
      (** The default translation used before May 2025. After that, many passes
          were made optional and disabled by default. *)
  | RawMir
      (** Emit the MIR as unmodified as possible. This is very imperfect for
          now, we should make more passes optional. *)
  | Fast  (** Skip as many optional transformations as possible. *)
  | Aeneas
  | Eurydice
  | Soteria
  | Tests

and serialization_format_arg = Json | Postcard | AllFormats

and target_info = {
  target_pointer_size : int;  (** The pointer size of the target in bytes. *)
  is_little_endian : bool;
      (** Whether the target platform uses little endian byte order. *)
}

(** The complete data of a Rust crate.

    A crate is mainly composed of 5 kinds of items:
    - Functions;
    - Type definitions;
    - Globals (constants and statics);
    - Trait declarations;
    - Trait implementations.

    These can each be found in the corresponding [IndexVec]. They are in an
    unspecified (though deterministic) order. If you need a more robust order,
    see [ordered_decls].

    To get a [TranslatedCrate], run [charon cargo] inside a Rust crate, then
    deserialize the resulting [crate_name.llbc] file using
    [[crate::deserialize_llbc]]. *)
and translated_crate = {
  crate_name : string;  (** The name of the crate. *)
  options : cli_options;
      (** The options used when calling Charon. Can be used to check that Charon
          was called with the options that a given consumer requires. *)
  target_information : (string * target_info) list;
      (** Information about each target platform for which the crate was
          translated. When translating a crate normally this will have a single
          entry; when using [--targets] this will have one entry per chosen
          target. *)
  files : file list;
      (** The source files composing the crate and its dependencies. Each
          [[Span]] refers to a byte range within one of these files. *)
  item_names : (item_id * name) list;
      (** The names of all registered items. Available so we can know the names
          even of items that failed to translate. Invariant: after translation,
          any existing [ItemId] must have an associated name, even if the
          corresponding item wasn't translated. *)
  assoc_item_names : assoc_item_names trait_decl_id_map;
      (** The names of all the registered associated items. Available so we can
          know the names even of items that failed to translate. Invariant:
          after translation, any existing [AssocItemId] must have an associated
          name, even if the corresponding item wasn't translated. *)
  short_names : (item_id * name) list;
      (** Short names, for items whose last PathElem is unique. *)
  type_decls : type_decl type_decl_id_map;
      (** The type definitions (structs, enums, ...). *)
  fun_decls : fun_decl fun_decl_id_map;
      (** The function definitions.

          Each item with a body becomes a function: actual functions, methods,
          and unevaluated consts/statics. *)
  global_decls : global_decl global_decl_id_map;
      (** The global definitions, which are constants, statics, and thread
          locals. *)
  trait_decls : trait_decl trait_decl_id_map;  (** The trait declarations. *)
  trait_impls : trait_impl trait_impl_id_map;  (** The trait implementations. *)
  ordered_decls : declaration_group list option;
      (** This contains a list of all the reachable items in the crate in a
          stable, logical order based on crate and file order, then further
          grouped and sorted such that every item comes after the items it
          depends on. Mutually-dependent groups of items are identified as such.
          This is meant for code-generation tools that want a stable output
          order.

          Not all the items in the [TranslatedCrate] are included: some trait
          impls are never referred to by reachable items so could in principle
          be removed from the crate, but we keep them around to be able to tell
          method implementations apart.

          [Some] after translation unless [--no-reorder-decls] is passed. *)
}
[@@deriving show]
