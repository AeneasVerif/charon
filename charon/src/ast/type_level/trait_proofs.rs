use crate::ast::*;
use crate::ids::IndexVec;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA};
use serde_state::{DeserializeState, SerializeState};

/// A reference to a trait.
///
/// This type is hash-consed, `TraitRefContents` contains the actual data.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[serde_state(state_implements = DedupSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct TraitRef(pub HashConsed<TraitRefContents>);

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct TraitRefContents {
    pub kind: TraitRefKind,
    /// Not necessary, but useful
    pub trait_decl_ref: PolyTraitDeclRef,
}

/// Identifier of a trait instance.
/// This is derived from the trait resolution.
///
/// Should be read as a path inside the trait clauses which apply to the current
/// definition. Note that every path designated by `TraitInstanceId` refers
/// to a *trait instance*, which is why the [`TraitRefKind::Clause`] variant may seem redundant
/// with some of the other variants.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    EnumIsA,
    EnumAsGetters,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum TraitRefKind {
    /// A specific top-level implementation item.
    TraitImpl(TraitImplRef),

    /// One of the local clauses.
    ///
    /// Example:
    /// ```text
    /// fn f<T>(...) where T : Foo
    ///                    ^^^^^^^
    ///                    Clause(0)
    /// ```
    Clause(ClauseDbVar),

    /// A parent clause
    ///
    /// Example:
    /// ```text
    /// trait Foo1 {}
    /// trait Foo2 { fn f(); }
    ///
    /// trait Bar : Foo1 + Foo2 {}
    ///             ^^^^   ^^^^
    ///                    parent clause 1
    ///     parent clause 0
    ///
    /// fn g<T : Bar>(x : T) {
    ///   x.f()
    ///   ^^^^^
    ///   Parent(Clause(0), 1)::f(x)
    ///                     ^
    ///                     parent clause 1 of clause 0
    /// }
    /// ```
    ParentClause(Box<TraitRef>, TraitClauseId),

    /// A clause defined on an associated type. This variant is only used during translation; after
    /// the `lift_associated_item_clauses` pass, clauses on items become `ParentClause`s.
    ///
    /// Example:
    /// ```text
    /// trait Foo {
    ///   type W: Bar0 + Bar1 // Bar1 contains a method bar1
    ///                  ^^^^
    ///               this is the clause 1 applying to W
    /// }
    ///
    /// fn f<T : Foo>(x : T::W) {
    ///   x.bar1();
    ///   ^^^^^^^
    ///   ItemClause(Clause(0), W, 1)
    ///                         ^^^^
    ///                         clause 1 from item W (from local clause 0)
    /// }
    /// ```
    ItemClause(Box<TraitRef>, AssocTypeId, TraitClauseId),

    /// The implicit `Self: Trait` clause. Present inside trait declarations, including trait
    /// method declarations. Not present in trait implementations as we can use `TraitImpl` intead.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("Self"))]
    SelfId,

    /// A trait implementation that is computed by the compiler, such as for built-in trait
    /// `Sized`. This morally points to an invisible `impl` block; as such it contains
    /// the information we may need from one.
    ///
    /// Also used as a placeholder for trait clauses that were stripped by the
    /// `--remove-adt-clauses` pass: the original `Clause` reference is replaced with a
    /// `BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }`. See
    /// [`BuiltinImplData::RemovedAdtClause`].
    BuiltinOrAuto {
        /// Metadata that identifies this impl.
        builtin_data: BuiltinImplData,
        /// Exactly like the same field on `TraitImpl`: the `TraitRef`s required to satisfy the
        /// implied predicates on the trait declaration. E.g. since `FnMut: FnOnce`, a built-in `T:
        /// FnMut` impl would have a `TraitRef` for `T: FnOnce`.
        parent_trait_refs: IndexVec<TraitClauseId, TraitRef>,
        /// The values of the associated types for this trait.
        types: IndexMap<AssocTypeId, TraitAssocTyImpl>,
        /// The vtable value for this builtin implementation, if we generated one.
        vtable: Option<GlobalDeclRef>,
    },

    /// The automatically-generated implementation for `dyn Trait`.
    Dyn,

    /// For error reporting.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("UnknownTrait"))]
    Unknown(String),
}

/// Describes a built-in impl. Mostly lists the implemented trait, sometimes with more details
/// about the contents of the implementation.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Builtin"))]
pub enum BuiltinImplData {
    /// Auto traits (defined with `auto trait ...`, also `Unpin`).
    Auto,

    Sized,
    MetaSized,
    PointeeSized,

    Copy,
    Clone,

    Tuple,
    Transmute,
    Unsize,

    Pointee,
    DiscriminantKind,

    Fn,
    FnMut,
    FnOnce,
    FnPtr,
    AsyncFn,
    AsyncFnMut,
    AsyncFnOnce,
    Coroutine,
    Future,

    /// Auto-trait used for `try_as_dyn` (see https://github.com/rust-lang/rust/issues/144361)
    TryAsDynCompatible,

    /// An impl of `Destruct` for a type with no drop glue.
    NoopDestruct,
    /// An impl of `Destruct` for a type parameter, which we could not resolve because
    /// `--add-drop-bounds` was not set.
    UntrackedDestruct,

    /// Placeholder used by the `--remove-adt-clauses` pass when it strips a trait clause from a
    /// type declaration. References to the removed clause are rewritten as
    /// `BuiltinOrAuto { builtin_data: RemovedAdtClause, .. }`.
    RemovedAdtClause,
}

impl TraitRef {
    pub fn new(kind: TraitRefKind, trait_decl_ref: PolyTraitDeclRef) -> Self {
        TraitRefContents {
            kind,
            trait_decl_ref,
        }
        .intern()
    }

    pub fn trait_id(&self) -> TraitDeclId {
        self.trait_decl_ref.skip_binder.id
    }

    /// Get mutable access to the contents. This cloned the value and will re-intern the modified
    /// value at the end of the function.
    pub fn with_contents_mut<R>(&mut self, f: impl FnOnce(&mut TraitRefContents) -> R) -> R {
        self.0.with_inner_mut(f)
    }

    pub fn vtable_ref<'a>(&'a self, krate: &'a TranslatedCrate) -> Option<&'a GlobalDeclRef> {
        match &self.kind {
            TraitRefKind::TraitImpl(impl_ref) => krate
                .trait_impls
                .get(impl_ref.id)
                .and_then(|timpl| timpl.vtable.as_ref()),
            TraitRefKind::BuiltinOrAuto { vtable, .. } => vtable.as_ref(),
            _ => None,
        }
    }
}

impl TraitRefContents {
    pub fn intern(self) -> TraitRef {
        TraitRef(HashConsed::new(self))
    }
}

impl BuiltinImplData {
    pub fn as_closure_kind(&self) -> Option<ClosureKind> {
        match self {
            BuiltinImplData::FnOnce => Some(ClosureKind::FnOnce),
            BuiltinImplData::FnMut => Some(ClosureKind::FnMut),
            BuiltinImplData::Fn => Some(ClosureKind::Fn),
            _ => None,
        }
    }
}

impl std::ops::Deref for TraitRef {
    type Target = TraitRefContents;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
