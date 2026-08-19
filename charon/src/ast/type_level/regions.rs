use crate::ast::*;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA};
use serde_state::{DeserializeState, SerializeState};

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    Hash,
    PartialOrd,
    Ord,
    EnumIsA,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("R"))]
pub enum Region {
    /// Region variable. See `DeBruijnVar` for details.
    Var(RegionDbVar),
    /// Static region
    Static,
    /// Body-local region, considered existentially-bound at the level of a body.
    Body(RegionId),
    /// Erased region
    Erased,
}
