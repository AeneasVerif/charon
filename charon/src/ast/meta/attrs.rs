use crate::ast::*;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::{EnumAsGetters, EnumIsA, EnumToGetters};
use serde::{Deserialize, Serialize};

/// `#[inline]` built-in attribute.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub enum InlineAttr {
    /// `#[inline]`
    Hint,
    /// `#[inline(never)]`
    Never,
    /// `#[inline(always)]`
    Always,
}

/// Attributes (`#[...]`).
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Attr"))]
pub enum Attribute {
    /// Do not translate the body of this item.
    /// Written `#[charon::opaque]`
    Opaque,
    /// Do not translate this item at all.
    /// Written `#[charon::exclude]`
    Exclude,
    /// Provide a new name that consumers of the llbc can use.
    /// Written `#[charon::rename("new_name")]`
    Rename(String),
    /// For enums only: rename the variants by pre-pending their names with the given prefix.
    /// Written `#[charon::variants_prefix("prefix_")]`.
    VariantsPrefix(String),
    /// Same as `VariantsPrefix`, but appends to the name instead of pre-pending.
    VariantsSuffix(String),
    /// The structure is treated as a transparent wrapper around its sole field.
    /// Written `#[charon::transparent]`.
    Transparent,
    /// An item annotated with `#[charon::precondition]`. This makes it a precondition for its
    /// parent item.
    IsPrecondition(ItemId),
    /// An item annotated with `#[charon::postcondition]`. This makes it a postcondition for its
    /// parent item.
    IsPostcondition(ItemId),
    /// An item that has a precondition that applies to it. The referenced item is a function the
    /// specifies the condition.
    HasPrecondition(FunDeclId),
    /// An item that has a postcondition that applies to it. The referenced item is a function the
    /// specifies the condition.
    HasPostcondition(FunDeclId),
    /// A doc-comment such as `/// ...`.
    DocComment(String),
    /// A built-in attribute.
    Builtin(#[drive(skip)] from_rustc::AttributeKind),
    /// None of the above.
    Unknown(RawAttribute),
}

/// A general attribute.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub struct RawAttribute {
    pub path: String,
    /// The arguments passed to the attribute, if any. We don't distinguish different delimiters or
    /// the `path = lit` case.
    pub args: Option<String>,
}

/// Information about the attributes and visibility of an item, field or variant..
#[derive(
    Debug, PartialEq, Eq, Default, Clone, Serialize, Deserialize, Drive, DriveMut, DriveTwo,
)]
pub struct AttrInfo {
    /// Attributes (`#[...]`).
    pub attributes: Vec<Attribute>,
    /// Inline hints (on functions only).
    pub inline: Option<InlineAttr>,
    /// The name computed from `charon::rename` and `charon::variants_prefix` attributes, if any.
    /// This provides a custom name that can be used by consumers of llbc. E.g. Aeneas uses this to
    /// rename definitions in the extracted code.
    pub rename: Option<String>,
    /// Whether this item is declared public. Impl blocks and closures don't have visibility
    /// modifiers; we arbitrarily set this to `false` for them.
    ///
    /// Note that this is different from being part of the crate's public API: to be part of the
    /// public API, an item has to also be reachable from public items in the crate root. For
    /// example:
    /// ```rust,ignore
    /// mod foo {
    ///     pub struct X;
    /// }
    /// mod bar {
    ///     pub fn something(_x: super::foo::X) {}
    /// }
    /// pub use bar::something; // exposes `X`
    /// ```
    /// Without the `pub use ...`, neither `X` nor `something` would be part of the crate's public
    /// API (this is called "pub-in-priv" items). With or without the `pub use`, we set `public =
    /// true`; computing item reachability is harder.
    pub public: bool,
}

impl AttrInfo {
    pub fn dummy_private() -> Self {
        AttrInfo {
            public: false,
            ..Default::default()
        }
    }

    pub fn dummy_public() -> Self {
        AttrInfo {
            public: true,
            ..Default::default()
        }
    }
}
