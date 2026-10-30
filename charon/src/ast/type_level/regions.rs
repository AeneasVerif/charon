use crate::ast::*;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA};
use serde_state::{DeserializeState, SerializeState};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(EnumIsA, EnumAsGetters)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("R"))]
pub enum Region {
    /// Region variable. See `DeBruijnVar` for details.
    Var(RegionDbVar),
    /// The least upper bound, in the outlives ordering, of the regions in this type.
    /// `'lub<T>: 'a` is equivalent to `T: 'a`.
    Lub(Ty),
    /// Static region
    Static,
    /// Body-local region, considered existentially-bound at the level of a body.
    Body(RegionId),
    /// Erased region
    Erased,
}
