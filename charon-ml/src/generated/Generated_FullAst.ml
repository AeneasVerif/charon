(** WARNING: this file is partially auto-generated. Do not edit `FullAst.ml` by
    hand. Edit `generate_ml/templates/FullAst.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/FullAst.ml` contains the manual definitions and some
    `(* __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`. *)

open Generated_GAst
open Generated_UllbcAst
open Generated_LlbcAst
open Generated_Types
open Generated_Values
open Generated_Expressions
open Generated_Meta
open Identifiers

(** The allocator functions that rustc's allocator shim links. *)
type allocator_method =
  | Alloc
  | Dealloc
  | Realloc
  | AllocZeroed
  | AllocErrorHandler
      (** The handler called on allocation failure, see
          [#[alloc_error_handler]]. *)

and rustc_arch =
  | RustcArchAArch64
  | RustcArchAmdGpu
  | RustcArchArm
  | RustcArchArm64EC
  | RustcArchAvr
  | RustcArchBpf
  | RustcArchCSky
  | RustcArchHexagon
  | RustcArchLoongArch32
  | RustcArchLoongArch64
  | RustcArchM68k
  | RustcArchMips
  | RustcArchMips32r6
  | RustcArchMips64
  | RustcArchMips64r6
  | RustcArchMsp430
  | RustcArchNvptx64
  | RustcArchPowerPC
  | RustcArchPowerPC64
  | RustcArchRiscV32
  | RustcArchRiscV64
  | RustcArchS390x
  | RustcArchSparc
  | RustcArchSparc64
  | RustcArchSpirV
  | RustcArchWasm32
  | RustcArchWasm64
  | RustcArchX86
  | RustcArchX86_64
  | RustcArchXtensa
  | RustcArchOther of string
      (** The vast majority of the time, the compiler deals with a fixed set of
          values, so it is convenient for them to be represented in an enum.
          However, it is possible to have arbitrary values in a target JSON file
          (which can be parsed when [--target] is specified). This might occur,
          for example, for an out-of-tree codegen backend that supports a value
          (e.g. architecture or OS) that rustc currently doesn't know about.
          This variant exists as an escape hatch for such cases. *)

and assoc_item_names = {
  types : trait_item_name list;
  methods : trait_item_name list;
  consts : trait_item_name list;
}

and rustc_binary_format =
  | RustcBinaryFormatCoff
  | RustcBinaryFormatElf
  | RustcBinaryFormatMachO
  | RustcBinaryFormatWasm
  | RustcBinaryFormatXcoff

(** The body of a function.

    A normal function has a body that's either structured or unstructured. These
    are two equivalent representations of the same function body, which only
    differ in how control-flow is represented. By default bodies are structured;
    passing [--ullbc] to Charon makes bodies unstructured.

    Besides these, some functions have virtual bodies or no body, see the doc
    for each variant. *)
and body =
  | UnstructuredBody of Generated_UllbcAst.block list gexpr_body
      (** Body represented as a control-flow graph (CFG), i.e. with numbered
          blocks and jumps/GOTOs between them. This is available when passing
          [--ullbc] to Charon.

          This is also the same structure as rustc's MIR, and is in fact a
          direct translation of it. *)
  | StructuredBody of Generated_LlbcAst.block gexpr_body
      (** Body represented with structured control flow, i.e. with nested
          [if]/[match]/[loop] blocks. This is available when [--ullbc] is not
          passed to Charon.

          This structure is recovered from the unstructured body in the
          [ullbc_to_llbc] pass. *)
  | TargetDispatchBody of (string * fun_decl_ref) list
      (** A façade body that dispatches to one of several per-target function
          bodies. This is created during multi-target merging (using [--target])
          to represent functions that have a different implementation across
          targets. *)
  | ExternBody of string * linked_extern
      (** Function declared in an [extern { ... }] block.

          Fields:
          - [symbol]: The foreign symbol name.
          - [definition]: The function that the linker binds this symbol to.
            Only computed with [--link-extern-fns]. *)
  | IntrinsicBody of string * string option list * fun_decl_ref option * bool
      (** Rust intrinsic function. This describes a "built-in" operation that
          must be handled by the codegen backend.

          Fields:
          - [name]: The intrinsic name.
          - [arg_names]: The argument names, None if not available.
          - [fallback]: A fallback body that backends can use if they don't
            implement the intrinsic themselves.
          - [fallback_is_spec]: Whether the fallback body is marked
            [#[miri::intrinsic_fallback_is_spec]], in which case it exactly
            describes the behavior of the intrinsic. Otherwise the fallback is
            only one of the valid implementations of the intrinsic, e.g. the
            fallback may have less UB or less non-determinism. *)
  | OpaqueBody
      (** A body that the user chose not to translate, based on opacity settings
          like [--include]/[--opaque]. *)
  | MissingBody
      (** A body that was not available.

          These can occur when using a sysroot that doesn't have MIR for all the
          standard library functions. This is the case of the sysroot that ships
          with every Rust toolchain, but Charon uses a custom-built sysroot that
          does. So this shouldn't happen unless you're passing [--sysroot] to
          charon. *)
  | ErrorBody of error
      (** We encountered an error while translating this body. *)

(** An enum representing possible values for [cfg(target_abi)]. This field is
    not forwarded to LLVM so it does not by itself affect codegen. See the
    [cfg_abi] field of [[TargetOptions]] for more details. *)
and rustc_cfg_abi =
  | RustcCfgAbiAbi64
  | RustcCfgAbiAbiV2
  | RustcCfgAbiAbiV2Hf
  | RustcCfgAbiEabi
  | RustcCfgAbiEabiHf
  | RustcCfgAbiElfV1
  | RustcCfgAbiElfV2
  | RustcCfgAbiFortanix
  | RustcCfgAbiIlp32
  | RustcCfgAbiIlp32e
  | RustcCfgAbiLlvm
  | RustcCfgAbiMacAbi
  | RustcCfgAbiPauthtest
  | RustcCfgAbiSim
  | RustcCfgAbiSoftFloat
  | RustcCfgAbiSpe
  | RustcCfgAbiUwp
  | RustcCfgAbiVecDefault
  | RustcCfgAbiX32
  | RustcCfgAbiV8Plus
  | RustcCfgAbiUnspecified
  | RustcCfgAbiOther of string
      (** The vast majority of the time, the compiler deals with a fixed set of
          values, so it is convenient for them to be represented in an enum.
          However, it is possible to have arbitrary values in a target JSON file
          (which can be parsed when [--target] is specified). This might occur,
          for example, for an out-of-tree codegen backend that supports a value
          (e.g. architecture or OS) that rustc currently doesn't know about.
          This variant exists as an escape hatch for such cases. *)

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

and rustc_env =
  | RustcEnvGnu
  | RustcEnvMacAbi
  | RustcEnvMlibc
  | RustcEnvMsvc
  | RustcEnvMusl
  | RustcEnvNewlib
  | RustcEnvNto70
  | RustcEnvNto71
  | RustcEnvNto71IoSock
  | RustcEnvOhos
  | RustcEnvRelibc
  | RustcEnvSgx
  | RustcEnvSim
  | RustcEnvP1
  | RustcEnvP2
  | RustcEnvP3
  | RustcEnvUclibc
  | RustcEnvV5
  | RustcEnvUnspecified
  | RustcEnvOther of string
      (** The vast majority of the time, the compiler deals with a fixed set of
          values, so it is convenient for them to be represented in an enum.
          However, it is possible to have arbitrary values in a target JSON file
          (which can be parsed when [--target] is specified). This might occur,
          for example, for an out-of-tree codegen backend that supports a value
          (e.g. architecture or OS) that rustc currently doesn't know about.
          This variant exists as an escape hatch for such cases. *)

(** A function definition *)
and fun_decl = {
  def_id : fun_decl_id;
  item_meta : item_meta;  (** The meta data associated with the declaration. *)
  generics : generic_params;
  signature : fun_sig;
      (** The signature contains the inputs/output types and ABI details. *)
  src : fun_source;
      (** The function kind: "regular" function, trait method declaration, etc.
      *)
  body : body;  (** The function body. *)
}

(** A (group of) top-level declaration(s), properly reordered. "G" stands for
    "generic" *)
and 'a0 g_declaration_group =
  | NonRecGroup of 'a0  (** A non-recursive declaration *)
  | RecGroup of 'a0 list  (** A (group of mutually) recursive declaration(s) *)

(** The function that the linker binds an extern function's symbol to. *)
and linked_extern =
  | StronglyLinked of fun_decl_ref
      (** A strong definition, e.g. [#[no_mangle]] or [#[export_name]]. *)
  | WeaklyLinked of fun_decl_ref list
      (** Weak definitions ([#[linkage = "weak"]]), which the linker only binds
          the symbol to if there's no strong definition. If there are several,
          the linker may pick any of them. *)
  | AllocatorShim of allocator_method * fun_decl_ref
      (** Linked to the default allocator through rustc's allocator shim. This
          needs to be handled separately, as the signatures aren't
          ABI-compatible: the arguments need to be transmuted (e.g. [Alignment]
          -> [usize]).

          Fields:
          - [method]
          - [default] *)
  | Unlinked
      (** No function of the crate or its dependencies is exported under this
          symbol. *)

and rustc_os =
  | RustcOsAix
  | RustcOsAmdHsa
  | RustcOsAndroid
  | RustcOsCuda
  | RustcOsCygwin
  | RustcOsDragonfly
  | RustcOsEmscripten
  | RustcOsEspIdf
  | RustcOsFreeBsd
  | RustcOsFuchsia
  | RustcOsHaiku
  | RustcOsHelenOs
  | RustcOsHermit
  | RustcOsHorizon
  | RustcOsHurd
  | RustcOsHyperlight
  | RustcOsIllumos
  | RustcOsIOs
  | RustcOsL4Re
  | RustcOsLinux
  | RustcOsLynxOs178
  | RustcOsMacOs
  | RustcOsManagarm
  | RustcOsMotor
  | RustcOsNetBsd
  | RustcOsNone
  | RustcOsNto
  | RustcOsNuttX
  | RustcOsOpenBsd
  | RustcOsPs3
  | RustcOsPsp
  | RustcOsPsx
  | RustcOsQnx
  | RustcOsQtee
  | RustcOsQurt
  | RustcOsRedox
  | RustcOsRtems
  | RustcOsSerenity
  | RustcOsSolaris
  | RustcOsSolidAsp3
  | RustcOsTeeOs
  | RustcOsTrusty
  | RustcOsTvOs
  | RustcOsUefi
  | RustcOsVexOs
  | RustcOsVisionOs
  | RustcOsVita
  | RustcOsVxWorks
  | RustcOsWasi
  | RustcOsWatchOs
  | RustcOsWindows
  | RustcOsXous
  | RustcOsZkvm
  | RustcOsUnknown
  | RustcOsOther of string
      (** The vast majority of the time, the compiler deals with a fixed set of
          values, so it is convenient for them to be represented in an enum.
          However, it is possible to have arbitrary values in a target JSON file
          (which can be parsed when [--target] is specified). This might occur,
          for example, for an out-of-tree codegen backend that supports a value
          (e.g. architecture or OS) that rustc currently doesn't know about.
          This variant exists as an escape hatch for such cases. *)

and rustc_panic_strategy =
  | RustcPanicStrategyUnwind
  | RustcPanicStrategyAbort
  | RustcPanicStrategyImmediateAbort

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

and runtime_checks = {
  ub_checks : bool;
  overflow_checks : bool;
  contract_checks : bool;
}

and target_info = {
  arch : rustc_arch;
      (** The target architecture, as seen by [cfg(target_arch)]. *)
  vendor : string;  (** The target vendor, as seen by [cfg(target_vendor)]. *)
  os : rustc_os;  (** The target OS, as seen by [cfg(target_os)]. *)
  env : rustc_env;  (** The target environment, as seen by [cfg(target_env)]. *)
  cfg_abi : rustc_cfg_abi;  (** The target ABI, as seen by [cfg(target_abi)]. *)
  families : string list;
      (** The target families, as seen by [cfg(target_family)] (e.g. [unix], or
          both [unix] and [wasm]), as rustc spells them. *)
  binary_format : rustc_binary_format;
      (** The binary format of the target's object files. *)
  panic_strategy : rustc_panic_strategy;
      (** The panic strategy used, which depends on the target but can be
          overridden with [-C panic]. *)
  target_pointer_size : int;  (** The pointer size of the target in bytes. *)
  is_little_endian : bool;
      (** Whether the target platform uses little endian byte order. *)
  c_enum_smallest_repr_ty : int_ty;
      (** The minimum size of a [[repr(C)]] enum. *)
  primitive_alignments : (scalar_type * int) list;
      (** Alignments for primitive types. *)
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
  preset : preset option;
      (** The preset used when calling Charon. Can be used to check that Charon
          was called with the preset that a given consumer requires. *)
  target_information : (string * target_info) list;
      (** Information about each target platform for which the crate was
          translated. When translating a crate normally this will have a single
          entry; when using [--targets] this will have one entry per chosen
          target. *)
  runtime_checks : runtime_checks;
      (** Values of the runtime checks enabled for this crate. *)
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
