use derive_generic_visitor::{Drive, DriveMut};
use serde_state::{DeserializeState, SerializeState};

use crate::ast::{
    ByteCount, ConstantExpr, HashConsSerializerState, IntTy, LiteralTy, RefKind, TargetTriple,
    TranslatedCrate, Ty, TyKind, TypeId, UIntTy,
};

/// The basic building blocks of symbolic layout information.
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum SymLayoutAtom {
    /// Symbolic size of type T, cf. `size_of<T>()`.
    SymSize(Ty),
    /// Symbolic alignment of type T, cf. `align_of<T>()`
    SymAlign(Ty),
    /// Concrete layout information as a scalar value. TODO: maybe just a usize etc.?
    Concrete(ByteCount),
}

impl SymLayoutAtom {
    /// For single-target translation, return the concrete pointer size,
    /// else the symbolic size of `*const ()`.
    pub fn mk_ptr(translated: &TranslatedCrate) -> Self {
        if translated.target_information.len() == 1 {
            Self::Concrete(translated.the_target_information().target_pointer_size)
        } else {
            Self::SymSize(Ty::new(TyKind::RawPtr(Ty::mk_unit(), RefKind::Shared)))
        }
    }

    pub fn mk_ptr_for(translated: &TranslatedCrate, target: &TargetTriple) -> Option<Self> {
        translated
            .target_information
            .get(target)
            .map(|target_info| Self::Concrete(target_info.target_pointer_size))
    }
}

/// Composite symbolic layout expressions.
///
/// `non_exhaustive` since we might need many more composite layouts.
/// TODO: remove once we have all composite descriptions we need.
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[non_exhaustive]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum SymLayoutComp {
    /// A single symbolic layout atom.
    Atom(SymLayoutAtom),
    /// The sum of its atoms.
    Sum(Vec<SymLayoutAtom>),
    /// An atom multiplied by a fixed scalar (e.g. `N` in [T;N]).
    Product {
        atom: SymLayoutAtom,
        multiplier: ConstantExpr,
    },
    /// The next multiple of `target_align` from `base`.
    AlignedTo {
        base: Box<SymLayoutComp>,
        target_align: SymLayoutAtom,
    },
    /// The maximum of these composite layout expressions.
    Max(Vec<SymLayoutComp>),
}

/// Symbolic layout information about a type's size and alignment.
///
/// TODO: would it make sense to also have enum-specific information here?
/// E.g. whether the enum could have/has a guaranteed niche?
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)]
pub struct SymbolicLayout {
    pub size: SymLayoutComp,
    pub alignment: SymLayoutComp,
}

impl SymbolicLayout {
    pub fn mk_concrete(size: ByteCount, alignment: ByteCount) -> Self {
        if size.is_multiple_of(alignment) {
            Self {
                size: SymLayoutComp::Atom(SymLayoutAtom::Concrete(size)),
                alignment: SymLayoutComp::Atom(SymLayoutAtom::Concrete(alignment)),
            }
        } else {
            panic!(
                "Type size {} not a multiple of alignment {}!",
                size, alignment
            )
        }
    }

    pub fn mk_array(elem_ty: &Ty, elem_num: &ConstantExpr) -> Self {
        Self {
            size: SymLayoutComp::Product {
                atom: SymLayoutAtom::SymSize(elem_ty.clone()),
                multiplier: elem_num.clone(),
            },
            alignment: SymLayoutComp::Atom(SymLayoutAtom::SymAlign(elem_ty.clone())),
        }
    }

    /// This is consistent with [`rustc_middle::ty::Ty::primitive_size`].
    pub fn mk_primitive(primitive: &LiteralTy, ptr_size: SymLayoutAtom) -> Self {
        let size = match primitive {
            LiteralTy::Int(IntTy::Isize) | LiteralTy::UInt(UIntTy::Usize) => {
                return Self {
                    size: SymLayoutComp::Atom(ptr_size.clone()),
                    alignment: SymLayoutComp::Atom(ptr_size),
                };
            }
            LiteralTy::Int(int_ty) => int_ty.target_size(0),
            LiteralTy::UInt(uint_ty) => uint_ty.target_size(0),
            LiteralTy::Float(float_ty) => float_ty.target_size(),
            LiteralTy::Bool => 1,
            LiteralTy::Char => 4,
        };
        Self::mk_concrete(size as ByteCount, size as ByteCount)
    }

    pub fn mk_symbolic(ty: Ty) -> Self {
        Self {
            size: SymLayoutComp::Atom(SymLayoutAtom::SymSize(ty.clone())),
            alignment: SymLayoutComp::Atom(SymLayoutAtom::SymAlign(ty)),
        }
    }

    pub fn for_ty(ty: &Ty, translated: &TranslatedCrate) -> Option<Self> {
        match ty.kind() {
            TyKind::Adt(type_decl_ref) => match &type_decl_ref.id {
                TypeId::Adt(type_decl_id) => translated
                    .type_decls
                    .get(*type_decl_id)
                    .unwrap()
                    .the_layout()
                    .map(|layout| layout.size_align.clone()),
                TypeId::Tuple => todo!(),
                TypeId::Builtin(_) => todo!(),
            },
            TyKind::TypeVar(_) => Some(Self::mk_symbolic(ty.clone())),
            TyKind::Literal(literal_ty) => Some(Self::mk_primitive(
                literal_ty,
                SymLayoutAtom::mk_ptr(translated),
            )),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => {
                // For this case we assume that metadata is always address-sized or a ZST,
                // and that we thus have a homogenous aggregate (cf. https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/ty/layout/type.TyAndLayout.html#method.homogeneous_aggregate).
                // Then, the two "fields" of the pointer/reference are of the same size, have the same alignment,
                // and are located next to each other with no padding.
                let meta = ty.get_ptr_metadata(translated).into_type();
                let ptr_size = SymLayoutAtom::mk_ptr(translated);
                Some(Self {
                    size: SymLayoutComp::Sum(vec![ptr_size.clone(), SymLayoutAtom::SymSize(meta)]),
                    alignment: SymLayoutComp::Atom(ptr_size),
                })
            }
            TyKind::TraitType(_, _, _) => todo!(),
            TyKind::FnPtr(_) => todo!(),
            TyKind::Array(elem_ty, elem_num) => Some(Self::mk_array(elem_ty, elem_num)),
            TyKind::Slice(_) | TyKind::DynTrait(_) => {
                todo!("No support for symbolic layouts of DSTs yet.")
            }
            _ => None,
        }
    }
}
