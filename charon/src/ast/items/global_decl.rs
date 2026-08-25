use crate::ast::*;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use serde_state::DeserializeState;
use serde_state::SerializeState;

/// A global variable definition (constant or static).
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct GlobalDecl {
    pub def_id: GlobalDeclId,
    /// The meta data associated with the declaration.
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    pub ty: Ty,
    /// The context of the global: distinguishes normal items from trait-associated items and
    /// vtable instances.
    pub src: GlobalSource,
    /// The kind of global (static or const).
    pub global_kind: GlobalKind,
    /// The value of this constant/static. By default this is a [`ConstantExprKind::Call`] to the
    /// initializer function that computes the value (the function uses the same generic parameters
    /// as the global).
    pub value: ConstantExpr,
}

#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
pub enum GlobalKind {
    /// A static.
    Static,
    /// A thread-local static.
    ThreadLocal,
    /// A const with a name (either top-level or an associated const in a trait).
    NamedConst,
    /// A const without a name:
    /// - An inline const expression (`const { 1 + 1 }`);
    /// - A const expression in a type (`[u8; sizeof::<T>()]`);
    /// - A promoted constant, automatically lifted from a body (`&0`).
    AnonConst,
}

/// Where a given global came from.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Global"))]
pub enum GlobalSource {
    /// A normal global.
    Normal,
    /// A default assoc const in a trait declaration.
    TraitDefault {
        /// The trait declaration the const belongs to.
        trait_ref: TraitDeclRef,
        /// The associated const this corresponds to.
        item_id: AssocConstId,
    },
    /// An associated const in a trait implementation.
    TraitImpl {
        /// The trait implementation the const belongs to.
        impl_ref: TraitImplRef,
        /// The trait declaration that the impl block implements.
        trait_ref: TraitDeclRef,
        /// The associated const this corresponds to.
        item_id: AssocConstId,
        /// True if the trait decl had a default value for this const and this item is a copy of
        /// the default item.
        reuses_default: bool,
    },
    /// Defines the vtable for a trait impl.
    VTableInstance {
        /// The originating impl. This is `None` in monomorphized mode: the vtable global itself
        /// identifies the concrete instantiation, so we don't translate an impl reference solely
        /// to record its provenance.
        impl_ref: Option<TraitImplRef>,
    },
}

impl GlobalDecl {
    /// If this global's value is a call to its initializer function, returns the initializer's id.
    pub fn init_fun_id(&self) -> Option<FunDeclId> {
        match &self.value.kind {
            ConstantExprKind::Call(fn_ptr, _) => match &*fn_ptr.kind {
                FnPtrKind::Fun(FunId::Regular(id)) => Some(*id),
                _ => None,
            },
            _ => None,
        }
    }
}
