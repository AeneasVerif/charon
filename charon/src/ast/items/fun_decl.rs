use crate::ast::*;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::EnumIsA;
use macros::VariantName;
use serde_state::DeserializeState;
use serde_state::SerializeState;

/// A function definition
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct FunDecl {
    pub def_id: FunDeclId,
    /// The meta data associated with the declaration.
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    /// The signature contains the inputs/output types and ABI details.
    pub signature: Box<FunSig>,
    /// The function kind: "regular" function, trait method declaration, etc.
    pub src: FunSource,
    /// The function body.
    pub body: Body,
}

/// A function signature.
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
pub struct FunSig {
    /// Is the function unsafe or not
    pub is_unsafe: bool,
    /// The calling convention of this function.
    pub abi: Abi,
    /// Whether this is a C-variadic function (its last parameter is `...`).
    pub is_variadic: bool,
    pub inputs: Vec<Ty>,
    pub output: Ty,
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    VariantName,
    EnumIsA,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[serde_state(stateless)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Abi"))]
pub enum Abi {
    Rust,
    C,
    /// Rust's spelling for the ABI, e.g. "C-unwind" or "system".
    Other(ustr::Ustr),
}

/// Where a given function came from.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Fun"))]
pub enum FunSource {
    /// A normal function.
    Normal,
    /// A default method in a trait declaration.
    TraitDefault {
        /// The trait declaration this item belongs to.
        trait_ref: TraitDeclRef,
        /// The method this corresponds to.
        // TODO: also include method generics so we can recover a full `FnPtr::TraitMethod`
        item_id: TraitMethodId,
    },
    /// A method in a trait implementation.
    TraitImpl {
        /// The trait implementation the method belongs to.
        impl_ref: TraitImplRef,
        /// The trait declaration that the impl block implements.
        trait_ref: TraitDeclRef,
        /// The method this corresponds to.
        // TODO: also include method generics so we can recover a full `FnPtr::TraitMethod`
        item_id: TraitMethodId,
        /// True if the trait decl had a default implementation for this method and this item is a
        /// copy of the default item.
        reuses_default: bool,
    },
    /// Wraps a concrete implementation of a method into a function that takes `dyn Trait` as its
    /// `Self` type. This shim casts the receiver to the known concrete type and calls the real
    /// method.
    VTableShim,
    /// The initializer for a global.
    GlobalInitializer(GlobalDeclRef),
    /// A target-specific variant behind a `TargetDispatch` façade. The dispatcher is the function
    /// with the `Body::TargetDispatch` body that dispatches to this function.
    TargetDependent { dispatcher: FunDeclRef },
}

impl FunDecl {
    /// Replace the generic parameters of this function with the ones given by the binder.
    pub fn substitute_params(self, subst: Binder<GenericArgs>) -> Self {
        let FunDecl {
            def_id,
            item_meta,
            generics: _,
            signature,
            src,
            body,
        } = self;
        let signature = signature.substitute(&subst.skip_binder);
        let src = src.substitute(&subst.skip_binder);
        let body = body.substitute(&subst.skip_binder);
        FunDecl {
            def_id,
            item_meta,
            generics: subst.params,
            signature,
            src,
            body,
        }
    }
}

impl Abi {
    pub fn rust() -> Self {
        Self::Rust
    }

    pub fn rust_name(&self) -> &str {
        match self {
            Self::Rust => "Rust",
            Self::C => "C",
            Self::Other(name) => name.as_str(),
        }
    }
}
