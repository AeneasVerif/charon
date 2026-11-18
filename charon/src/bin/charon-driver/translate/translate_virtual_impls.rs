use crate::hax;
use crate::translate::translate_crate::VirtualImplKind;
use charon_lib::ast::*;

impl VirtualImplKind {
    pub fn virtual_trait(self) -> hax::VirtualTrait {
        match self {
            VirtualImplKind::Destruct => hax::VirtualTrait::Destruct,
            VirtualImplKind::Callable(ClosureKind::FnOnce) => hax::VirtualTrait::FnOnce,
            VirtualImplKind::Callable(ClosureKind::FnMut) => hax::VirtualTrait::FnMut,
            VirtualImplKind::Callable(ClosureKind::Fn) => hax::VirtualTrait::Fn,
        }
    }

    /// Whether the method we generate takes `self` by reference. If so, it takes an extra lifetime
    /// parameter for that borrow.
    pub fn has_self_borrow(self) -> bool {
        !matches!(self, VirtualImplKind::Callable(ClosureKind::FnOnce))
    }

    /// The name of the method we generate.
    pub fn method_path_elem(self) -> PathElem {
        match self {
            VirtualImplKind::Destruct => {
                PathElem::Builtin(BuiltinPathElem::DropGlue, Disambiguator::ZERO)
            }
            VirtualImplKind::Callable(kind) => {
                PathElem::Ident(kind.method_name().to_string(), Disambiguator::ZERO)
            }
        }
    }
}
