(** WARNING: this file is partially auto-generated. Do not edit `src/Meta.ml` by
    hand. Edit `templates/Meta.ml` instead, or improve the code generation tool
    so avoid the need for hand-writing things.

    `templates/Meta.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`. *)

type path_buf = string [@@deriving show, ord, eq]

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
          of the crate's public API (this is called 'pub-in-priv' items). With
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
          [#[charon::rename('new_name')]] *)
  | AttrVariantsPrefix of string
      (** For enums only: rename the variants by pre-pending their names with
          the given prefix. Written [#[charon::variants_prefix('prefix_')]]. *)
  | AttrVariantsSuffix of string
      (** Same as [VariantsPrefix], but appends to the name instead of
          pre-pending. *)
  | AttrTransparent
      (** The structure is treated as a transparent wrapper around its sole
          field. Written [#[charon::transparent]]. *)
  | AttrBuiltin of builtin_attr  (** A parsed built-in rustc attribute. *)
  | AttrDocComment of string  (** A doc-comment such as [/// ...]. *)
  | AttrUnknown of raw_attribute  (** A non-charon-specific attribute. *)

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
    'collapsed' into a single semantic attribute. For example:
    {@rust[
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
and builtin_attr =
  | BuiltinAttrAutomaticallyDerived
      (** Represents [#[automatically_derived]] *)
  | BuiltinAttrCold  (** Represents [#[cold]]. *)
  | BuiltinAttrEiiDeclaration of builtin_attr_eii_decl
      (** Implementation detail of [#[eii]] *)
  | BuiltinAttrEiiImpls of builtin_attr_eii_impl list
      (** Implementation detail of [#[eii]] *)
  | BuiltinAttrFundamental  (** Represents [#[fundamental]]. *)
  | BuiltinAttrIgnore of span * string option
      (** Represents [#[ignore]]

          Fields:
          - [span]
          - [reason]: ignore can optionally have a reason:
            [#[ignore = 'reason this is ignored']] *)
  | BuiltinAttrInline of builtin_attr_inline_attr * span
      (** Represents [#[inline]] and [#[rustc_force_inline]]. *)
  | BuiltinAttrLang of builtin_attr_lang_item  (** Represents [#[lang]] *)
  | BuiltinAttrMayDangle of span
      (** Represents
          [[#[may_dangle]]](https://std-dev-guide.rust-lang.org/tricky/may-dangle.html).
      *)
  | BuiltinAttrNaked of span  (** Represents [#[naked]] *)
  | BuiltinAttrNoLink  (** Represents [#[no_link]] *)
  | BuiltinAttrNoMangle of span  (** Represents [#[no_mangle]] *)
  | BuiltinAttrNonExhaustive of span  (** Represents [#[non_exhaustive]] *)
  | BuiltinAttrOptimize of builtin_attr_optimize_attr * span
      (** Represents [#[optimize(size|speed)]] *)
  | BuiltinAttrRustcDiagnosticItem of string
      (** Represents [#[rustc_diagnostic_item]] *)
  | BuiltinAttrRustcIntrinsic  (** Represents [#[rustc_intrinsic]] *)
  | BuiltinAttrTargetFeature of (string * span) list * span * bool
      (** Represents [#[target_feature(enable = '...')]] and
          [#[unsafe(force_target_feature(enable = '...')]].

          Fields:
          - [features]
          - [attr_span]
          - [was_forced] *)
  | BuiltinAttrTrackCaller of span  (** Represents [#[track_caller]] *)

and builtin_attr_eii_decl = {
  foreign_item : string;
  impl_unsafe : bool;  (** whether or not it is unsafe to implement this EII *)
  name : builtin_attr_ident;
}

and builtin_attr_eii_impl = {
  resolution : builtin_attr_eii_impl_resolution;
  impl_marked_unsafe : bool;
  span : span;
  inner_span : span;
  is_default : bool;
}

and builtin_attr_eii_impl_resolution =
  | BuiltinAttrEiiImplResolutionMacro of string
      (** Usually, finding the extern item that an EII implementation implements
          means finding the defid of the associated attribute macro, and looking
          at *its* attributes to find what foreign item its associated with. *)
  | BuiltinAttrEiiImplResolutionKnown of builtin_attr_eii_decl
      (** Sometimes though, we already know statically and can skip some name
          resolution. Stored together with the eii's name for diagnostics. *)
  | BuiltinAttrEiiImplResolutionError of string
      (** For when resolution failed, but we want to continue compilation *)

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
  | NotReal of string  (** A 'not real' file name (macro, query, etc.) *)

and builtin_attr_ident = {
  name : string;
      (** [name] should never be the empty symbol. If you are considering that,
          you are probably conflating 'empty identifier with 'no identifier' and
          you should use [Option<Ident>] instead. Trying to construct an [Ident]
          with an empty name will trigger debug assertions. *)
  span : span;
}

(** [#[inline]] built-in attribute. *)
and inline_attr =
  | Hint  (** [#[inline]] *)
  | Never  (** [#[inline(never)]] *)
  | Always  (** [#[inline(always)]] *)

and builtin_attr_inline_attr =
  | BuiltinAttrInlineAttrNone
  | BuiltinAttrInlineAttrHint
  | BuiltinAttrInlineAttrAlways
  | BuiltinAttrInlineAttrNever
  | BuiltinAttrInlineAttrForce of span * string option
      (** [#[rustc_force_inline]] forces inlining to happen in the MIR inliner -
          it reports an error if the inlining cannot happen. It is limited to
          only free functions so that the calls can always be resolved.

          Fields:
          - [attr_span]
          - [reason] *)

(** A representation of all the valid lang items in Rust. *)
and builtin_attr_lang_item =
  | BuiltinAttrLangItemSized  (**The [sized] lang item. *)
  | BuiltinAttrLangItemMetaSized  (**The [meta_sized] lang item. *)
  | BuiltinAttrLangItemPointeeSized  (**The [pointee_sized] lang item. *)
  | BuiltinAttrLangItemUnsize  (**The [unsize] lang item. *)
  | BuiltinAttrLangItemAlignOf  (**The [mem_align_const] lang item. *)
  | BuiltinAttrLangItemSizeOf  (**The [mem_size_const] lang item. *)
  | BuiltinAttrLangItemOffsetOf  (**The [offset_of] lang item. *)
  | BuiltinAttrLangItemStructuralPeq
      (** The [structural_peq] lang item. Trait injected by
          [#[derive(PartialEq)]], (i.e. 'Partial EQ'). *)
  | BuiltinAttrLangItemCopy  (**The [copy] lang item. *)
  | BuiltinAttrLangItemClone  (**The [clone] lang item. *)
  | BuiltinAttrLangItemCloneFn  (**The [clone_fn] lang item. *)
  | BuiltinAttrLangItemUseCloned  (**The [use_cloned] lang item. *)
  | BuiltinAttrLangItemTrivialClone  (**The [trivial_clone] lang item. *)
  | BuiltinAttrLangItemSync  (**The [sync] lang item. *)
  | BuiltinAttrLangItemDiscriminantKind
      (**The [discriminant_kind] lang item. *)
  | BuiltinAttrLangItemDiscriminant
      (** The [discriminant_type] lang item. The associated item of the
          [DiscriminantKind] trait. *)
  | BuiltinAttrLangItemPointeeTrait  (**The [pointee_trait] lang item. *)
  | BuiltinAttrLangItemMetadata  (**The [metadata_type] lang item. *)
  | BuiltinAttrLangItemDynMetadata  (**The [dyn_metadata] lang item. *)
  | BuiltinAttrLangItemFreeze  (**The [freeze] lang item. *)
  | BuiltinAttrLangItemUnsafeUnpin  (**The [unsafe_unpin] lang item. *)
  | BuiltinAttrLangItemFnPtrTrait  (**The [fn_ptr_trait] lang item. *)
  | BuiltinAttrLangItemFnPtrAddr  (**The [fn_ptr_addr] lang item. *)
  | BuiltinAttrLangItemDrop  (**The [drop] lang item. *)
  | BuiltinAttrLangItemDestruct  (**The [destruct] lang item. *)
  | BuiltinAttrLangItemAsyncDrop  (**The [async_drop] lang item. *)
  | BuiltinAttrLangItemAsyncDropInPlace
      (**The [async_drop_in_place] lang item. *)
  | BuiltinAttrLangItemCoerceUnsized  (**The [coerce_unsized] lang item. *)
  | BuiltinAttrLangItemDispatchFromDyn  (**The [dispatch_from_dyn] lang item. *)
  | BuiltinAttrLangItemTransmuteOpts  (**The [transmute_opts] lang item. *)
  | BuiltinAttrLangItemTransmuteTrait  (**The [transmute_trait] lang item. *)
  | BuiltinAttrLangItemAdd  (**The [add] lang item. *)
  | BuiltinAttrLangItemSub  (**The [sub] lang item. *)
  | BuiltinAttrLangItemMul  (**The [mul] lang item. *)
  | BuiltinAttrLangItemDiv  (**The [div] lang item. *)
  | BuiltinAttrLangItemRem  (**The [rem] lang item. *)
  | BuiltinAttrLangItemNeg  (**The [neg] lang item. *)
  | BuiltinAttrLangItemNot  (**The [not] lang item. *)
  | BuiltinAttrLangItemBitXor  (**The [bitxor] lang item. *)
  | BuiltinAttrLangItemBitAnd  (**The [bitand] lang item. *)
  | BuiltinAttrLangItemBitOr  (**The [bitor] lang item. *)
  | BuiltinAttrLangItemShl  (**The [shl] lang item. *)
  | BuiltinAttrLangItemShr  (**The [shr] lang item. *)
  | BuiltinAttrLangItemAddAssign  (**The [add_assign] lang item. *)
  | BuiltinAttrLangItemSubAssign  (**The [sub_assign] lang item. *)
  | BuiltinAttrLangItemMulAssign  (**The [mul_assign] lang item. *)
  | BuiltinAttrLangItemDivAssign  (**The [div_assign] lang item. *)
  | BuiltinAttrLangItemRemAssign  (**The [rem_assign] lang item. *)
  | BuiltinAttrLangItemBitXorAssign  (**The [bitxor_assign] lang item. *)
  | BuiltinAttrLangItemBitAndAssign  (**The [bitand_assign] lang item. *)
  | BuiltinAttrLangItemBitOrAssign  (**The [bitor_assign] lang item. *)
  | BuiltinAttrLangItemShlAssign  (**The [shl_assign] lang item. *)
  | BuiltinAttrLangItemShrAssign  (**The [shr_assign] lang item. *)
  | BuiltinAttrLangItemIndex  (**The [index] lang item. *)
  | BuiltinAttrLangItemIndexMut  (**The [index_mut] lang item. *)
  | BuiltinAttrLangItemUnsafeCell  (**The [unsafe_cell] lang item. *)
  | BuiltinAttrLangItemUnsafePinned  (**The [unsafe_pinned] lang item. *)
  | BuiltinAttrLangItemVaArgSafe  (**The [va_arg_safe] lang item. *)
  | BuiltinAttrLangItemVaList  (**The [va_list] lang item. *)
  | BuiltinAttrLangItemDeref  (**The [deref] lang item. *)
  | BuiltinAttrLangItemDerefMut  (**The [deref_mut] lang item. *)
  | BuiltinAttrLangItemDerefPure  (**The [deref_pure] lang item. *)
  | BuiltinAttrLangItemDerefTarget  (**The [deref_target] lang item. *)
  | BuiltinAttrLangItemReceiver  (**The [receiver] lang item. *)
  | BuiltinAttrLangItemReceiverTarget  (**The [receiver_target] lang item. *)
  | BuiltinAttrLangItemLegacyReceiver  (**The [legacy_receiver] lang item. *)
  | BuiltinAttrLangItemFn  (**The [Fn] lang item. *)
  | BuiltinAttrLangItemFnMut  (**The [fn_mut] lang item. *)
  | BuiltinAttrLangItemFnOnce  (**The [fn_once] lang item. *)
  | BuiltinAttrLangItemAsyncFn  (**The [async_fn] lang item. *)
  | BuiltinAttrLangItemAsyncFnMut  (**The [async_fn_mut] lang item. *)
  | BuiltinAttrLangItemAsyncFnOnce  (**The [async_fn_once] lang item. *)
  | BuiltinAttrLangItemAsyncFnOnceOutput
      (**The [async_fn_once_output] lang item. *)
  | BuiltinAttrLangItemCallOnceFuture  (**The [call_once_future] lang item. *)
  | BuiltinAttrLangItemCallRefFuture  (**The [call_ref_future] lang item. *)
  | BuiltinAttrLangItemAsyncFnKindHelper
      (**The [async_fn_kind_helper] lang item. *)
  | BuiltinAttrLangItemAsyncFnKindUpvars
      (**The [async_fn_kind_upvars] lang item. *)
  | BuiltinAttrLangItemFnOnceOutput  (**The [fn_once_output] lang item. *)
  | BuiltinAttrLangItemIterator  (**The [iterator] lang item. *)
  | BuiltinAttrLangItemFusedIterator  (**The [fused_iterator] lang item. *)
  | BuiltinAttrLangItemFuture  (**The [future_trait] lang item. *)
  | BuiltinAttrLangItemFutureOutput  (**The [future_output] lang item. *)
  | BuiltinAttrLangItemAsyncIterator  (**The [async_iterator] lang item. *)
  | BuiltinAttrLangItemCoroutineState  (**The [coroutine_state] lang item. *)
  | BuiltinAttrLangItemCoroutine  (**The [coroutine] lang item. *)
  | BuiltinAttrLangItemCoroutineReturn  (**The [coroutine_return] lang item. *)
  | BuiltinAttrLangItemCoroutineYield  (**The [coroutine_yield] lang item. *)
  | BuiltinAttrLangItemCoroutineResume  (**The [coroutine_resume] lang item. *)
  | BuiltinAttrLangItemUnpin  (**The [unpin] lang item. *)
  | BuiltinAttrLangItemPin  (**The [pin] lang item. *)
  | BuiltinAttrLangItemOrderingEnum  (**The [Ordering] lang item. *)
  | BuiltinAttrLangItemPartialEq  (**The [eq] lang item. *)
  | BuiltinAttrLangItemPartialOrd  (**The [partial_ord] lang item. *)
  | BuiltinAttrLangItemCVoid  (**The [c_void] lang item. *)
  | BuiltinAttrLangItemType  (**The [type_info] lang item. *)
  | BuiltinAttrLangItemTypeId  (**The [type_id] lang item. *)
  | BuiltinAttrLangItemPanic  (**The [panic] lang item. *)
  | BuiltinAttrLangItemPanicNounwind  (**The [panic_nounwind] lang item. *)
  | BuiltinAttrLangItemPanicFmt  (**The [panic_fmt] lang item. *)
  | BuiltinAttrLangItemPanicDisplay  (**The [panic_display] lang item. *)
  | BuiltinAttrLangItemConstPanicFmt  (**The [const_panic_fmt] lang item. *)
  | BuiltinAttrLangItemPanicBoundsCheck
      (**The [panic_bounds_check] lang item. *)
  | BuiltinAttrLangItemPanicMisalignedPointerDereference
      (**The [panic_misaligned_pointer_dereference] lang item. *)
  | BuiltinAttrLangItemPanicInfo  (**The [panic_info] lang item. *)
  | BuiltinAttrLangItemPanicLocation  (**The [panic_location] lang item. *)
  | BuiltinAttrLangItemPanicImpl  (**The [panic_impl] lang item. *)
  | BuiltinAttrLangItemPanicCannotUnwind
      (**The [panic_cannot_unwind] lang item. *)
  | BuiltinAttrLangItemPanicInCleanup  (**The [panic_in_cleanup] lang item. *)
  | BuiltinAttrLangItemPanicAddOverflow
      (** The [panic_const_add_overflow] lang item. Constant panic messages,
          used for codegen of MIR asserts. *)
  | BuiltinAttrLangItemPanicSubOverflow
      (**The [panic_const_sub_overflow] lang item. *)
  | BuiltinAttrLangItemPanicMulOverflow
      (**The [panic_const_mul_overflow] lang item. *)
  | BuiltinAttrLangItemPanicDivOverflow
      (**The [panic_const_div_overflow] lang item. *)
  | BuiltinAttrLangItemPanicRemOverflow
      (**The [panic_const_rem_overflow] lang item. *)
  | BuiltinAttrLangItemPanicNegOverflow
      (**The [panic_const_neg_overflow] lang item. *)
  | BuiltinAttrLangItemPanicShrOverflow
      (**The [panic_const_shr_overflow] lang item. *)
  | BuiltinAttrLangItemPanicShlOverflow
      (**The [panic_const_shl_overflow] lang item. *)
  | BuiltinAttrLangItemPanicDivZero
      (**The [panic_const_div_by_zero] lang item. *)
  | BuiltinAttrLangItemPanicRemZero
      (**The [panic_const_rem_by_zero] lang item. *)
  | BuiltinAttrLangItemPanicCoroutineResumed
      (**The [panic_const_coroutine_resumed] lang item. *)
  | BuiltinAttrLangItemPanicAsyncFnResumed
      (**The [panic_const_async_fn_resumed] lang item. *)
  | BuiltinAttrLangItemPanicAsyncGenFnResumed
      (**The [panic_const_async_gen_fn_resumed] lang item. *)
  | BuiltinAttrLangItemPanicGenFnNone
      (**The [panic_const_gen_fn_none] lang item. *)
  | BuiltinAttrLangItemPanicCoroutineResumedPanic
      (**The [panic_const_coroutine_resumed_panic] lang item. *)
  | BuiltinAttrLangItemPanicAsyncFnResumedPanic
      (**The [panic_const_async_fn_resumed_panic] lang item. *)
  | BuiltinAttrLangItemPanicAsyncGenFnResumedPanic
      (**The [panic_const_async_gen_fn_resumed_panic] lang item. *)
  | BuiltinAttrLangItemPanicGenFnNonePanic
      (**The [panic_const_gen_fn_none_panic] lang item. *)
  | BuiltinAttrLangItemPanicNullPointerDereference
      (**The [panic_null_pointer_dereference] lang item. *)
  | BuiltinAttrLangItemPanicInvalidEnumConstruction
      (**The [panic_invalid_enum_construction] lang item. *)
  | BuiltinAttrLangItemPanicCoroutineResumedDrop
      (**The [panic_const_coroutine_resumed_drop] lang item. *)
  | BuiltinAttrLangItemPanicAsyncFnResumedDrop
      (**The [panic_const_async_fn_resumed_drop] lang item. *)
  | BuiltinAttrLangItemPanicAsyncGenFnResumedDrop
      (**The [panic_const_async_gen_fn_resumed_drop] lang item. *)
  | BuiltinAttrLangItemPanicGenFnNoneDrop
      (**The [panic_const_gen_fn_none_drop] lang item. *)
  | BuiltinAttrLangItemBeginPanic
      (** The [begin_panic] lang item. libstd panic entry point. Necessary for
          const eval to be able to catch it *)
  | BuiltinAttrLangItemFormatArgument  (**The [format_argument] lang item. *)
  | BuiltinAttrLangItemFormatArguments  (**The [format_arguments] lang item. *)
  | BuiltinAttrLangItemDropGlue  (**The [drop_glue] lang item. *)
  | BuiltinAttrLangItemAllocLayout  (**The [alloc_layout] lang item. *)
  | BuiltinAttrLangItemStart
      (** The [start] lang item. For all binary crates without [#![no_main]],
          Rust will generate a 'main' function. The exact name and signature are
          target-dependent. The 'main' function will invoke this lang item,
          passing it the [argc] and [argv] (or null, if those don't exist on the
          current target) as well as the user-defined [fn main] from the binary
          crate. *)
  | BuiltinAttrLangItemEhPersonality  (**The [eh_personality] lang item. *)
  | BuiltinAttrLangItemEhCatchTypeinfo  (**The [eh_catch_typeinfo] lang item. *)
  | BuiltinAttrLangItemCompilerMove  (**The [compiler_move] lang item. *)
  | BuiltinAttrLangItemCompilerCopy  (**The [compiler_copy] lang item. *)
  | BuiltinAttrLangItemOwnedBox  (**The [owned_box] lang item. *)
  | BuiltinAttrLangItemGlobalAlloc  (**The [global_alloc_ty] lang item. *)
  | BuiltinAttrLangItemPhantomData  (**The [phantom_data] lang item. *)
  | BuiltinAttrLangItemManuallyDrop  (**The [manually_drop] lang item. *)
  | BuiltinAttrLangItemMaybeDangling  (**The [maybe_dangling] lang item. *)
  | BuiltinAttrLangItemBikeshedGuaranteedNoDrop
      (**The [bikeshed_guaranteed_no_drop] lang item. *)
  | BuiltinAttrLangItemMaybeUninit  (**The [maybe_uninit] lang item. *)
  | BuiltinAttrLangItemTermination  (**The [termination] lang item. *)
  | BuiltinAttrLangItemTry  (**The [Try] lang item. *)
  | BuiltinAttrLangItemTuple  (**The [tuple_trait] lang item. *)
  | BuiltinAttrLangItemSliceLen  (**The [slice_len_fn] lang item. *)
  | BuiltinAttrLangItemTryTraitFromResidual
      (**The [from_residual] lang item. *)
  | BuiltinAttrLangItemTryTraitFromOutput  (**The [from_output] lang item. *)
  | BuiltinAttrLangItemTryTraitBranch  (**The [branch] lang item. *)
  | BuiltinAttrLangItemTryTraitFromYeet  (**The [from_yeet] lang item. *)
  | BuiltinAttrLangItemResidualIntoTryType  (**The [into_try_type] lang item. *)
  | BuiltinAttrLangItemCoercePointeeValidated
      (**The [coerce_pointee_validated] lang item. *)
  | BuiltinAttrLangItemConstParamTy  (**The [const_param_ty] lang item. *)
  | BuiltinAttrLangItemPoll  (**The [Poll] lang item. *)
  | BuiltinAttrLangItemPollReady  (**The [Ready] lang item. *)
  | BuiltinAttrLangItemPollPending  (**The [Pending] lang item. *)
  | BuiltinAttrLangItemAsyncGenReady  (**The [AsyncGenReady] lang item. *)
  | BuiltinAttrLangItemAsyncGenPending  (**The [AsyncGenPending] lang item. *)
  | BuiltinAttrLangItemAsyncGenFinished  (**The [AsyncGenFinished] lang item. *)
  | BuiltinAttrLangItemResumeTy  (**The [ResumeTy] lang item. *)
  | BuiltinAttrLangItemGetContext  (**The [get_context] lang item. *)
  | BuiltinAttrLangItemContext  (**The [Context] lang item. *)
  | BuiltinAttrLangItemFuturePoll  (**The [poll] lang item. *)
  | BuiltinAttrLangItemAsyncIteratorPollNext
      (**The [async_iterator_poll_next] lang item. *)
  | BuiltinAttrLangItemIntoAsyncIterIntoIter
      (**The [into_async_iter_into_iter] lang item. *)
  | BuiltinAttrLangItemOption  (**The [Option] lang item. *)
  | BuiltinAttrLangItemOptionSome  (**The [Some] lang item. *)
  | BuiltinAttrLangItemOptionNone  (**The [None] lang item. *)
  | BuiltinAttrLangItemResultOk  (**The [Ok] lang item. *)
  | BuiltinAttrLangItemResultErr  (**The [Err] lang item. *)
  | BuiltinAttrLangItemControlFlowContinue  (**The [Continue] lang item. *)
  | BuiltinAttrLangItemControlFlowBreak  (**The [Break] lang item. *)
  | BuiltinAttrLangItemIntoFutureIntoFuture  (**The [into_future] lang item. *)
  | BuiltinAttrLangItemIntoIterIntoIter  (**The [into_iter] lang item. *)
  | BuiltinAttrLangItemIteratorNext  (**The [next] lang item. *)
  | BuiltinAttrLangItemPinNewUnchecked  (**The [new_unchecked] lang item. *)
  | BuiltinAttrLangItemRangeFrom  (**The [RangeFrom] lang item. *)
  | BuiltinAttrLangItemRangeFull  (**The [RangeFull] lang item. *)
  | BuiltinAttrLangItemRangeInclusiveStruct
      (**The [RangeInclusive] lang item. *)
  | BuiltinAttrLangItemRangeInclusiveNew
      (**The [range_inclusive_new] lang item. *)
  | BuiltinAttrLangItemRange  (**The [Range] lang item. *)
  | BuiltinAttrLangItemRangeToInclusive  (**The [RangeToInclusive] lang item. *)
  | BuiltinAttrLangItemRangeTo  (**The [RangeTo] lang item. *)
  | BuiltinAttrLangItemRangeMax  (**The [RangeMax] lang item. *)
  | BuiltinAttrLangItemRangeMin  (**The [RangeMin] lang item. *)
  | BuiltinAttrLangItemRangeSub  (**The [RangeSub] lang item. *)
  | BuiltinAttrLangItemRangeFromCopy  (**The [RangeFromCopy] lang item. *)
  | BuiltinAttrLangItemRangeCopy  (**The [RangeCopy] lang item. *)
  | BuiltinAttrLangItemRangeInclusiveCopy
      (**The [RangeInclusiveCopy] lang item. *)
  | BuiltinAttrLangItemRangeToInclusiveCopy
      (**The [RangeToInclusiveCopy] lang item. *)
  | BuiltinAttrLangItemString  (**The [String] lang item. *)
  | BuiltinAttrLangItemCStr  (**The [CStr] lang item. *)
  | BuiltinAttrLangItemContractBuildCheckEnsures
      (**The [contract_build_check_ensures] lang item. *)
  | BuiltinAttrLangItemContractCheckRequires
      (**The [contract_check_requires] lang item. *)
  | BuiltinAttrLangItemDefaultTrait4  (**The [default_trait4] lang item. *)
  | BuiltinAttrLangItemDefaultTrait3  (**The [default_trait3] lang item. *)
  | BuiltinAttrLangItemDefaultTrait2  (**The [default_trait2] lang item. *)
  | BuiltinAttrLangItemDefaultTrait1  (**The [default_trait1] lang item. *)
  | BuiltinAttrLangItemContractCheckEnsures
      (**The [contract_check_ensures] lang item. *)
  | BuiltinAttrLangItemReborrow  (**The [reborrow] lang item. *)
  | BuiltinAttrLangItemCoerceShared  (**The [coerce_shared] lang item. *)
  | BuiltinAttrLangItemFieldRepresentingType
      (**The [field_representing_type] lang item. *)
  | BuiltinAttrLangItemField  (**The [field] lang item. *)
  | BuiltinAttrLangItemFieldBase  (**The [field_base] lang item. *)
  | BuiltinAttrLangItemFieldType  (**The [field_type] lang item. *)
  | BuiltinAttrLangItemFieldOffset  (**The [field_offset] lang item. *)
  | BuiltinAttrLangItemFrom  (**The [From] lang item. *)

and loc = {
  line : int;  (** The (1-based) line number. *)
  col : int;  (** The (0-based) column offset. *)
}

and builtin_attr_optimize_attr =
  | BuiltinAttrOptimizeAttrDefault  (** No [#[optimize(..)]] attribute *)
  | BuiltinAttrOptimizeAttrDoNotOptimize  (** [#[optimize(none)]] *)
  | BuiltinAttrOptimizeAttrSpeed  (** [#[optimize(speed)]] *)
  | BuiltinAttrOptimizeAttrSize  (** [#[optimize(size)]] *)

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
[@@deriving show, ord, eq]
