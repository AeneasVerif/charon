use crate::translate::translate_crate::VirtualImplKind;
use charon_lib::ast::*;

impl VirtualImplKind {
    pub fn trait_impl_source(self) -> TraitImplSource {
        match self {
            VirtualImplKind::Destruct => TraitImplSource::Destruct,
            VirtualImplKind::Callable(kind) => TraitImplSource::Closure { kind },
        }
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
