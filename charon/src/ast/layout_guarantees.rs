use std::{collections::HashSet, ops::AddAssign};

use derive_generic_visitor::{Drive, DriveMut};
use serde_state::{DeserializeState, SerializeState};

use crate::ast::{
    BuiltinTy, ByteCount, ConstantExpr, ConstantExprKind, FloatTy, HashConsSerializerState, IntTy,
    Literal, LiteralTy, ScalarValue, SeqHashMap, TargetTriple, TranslatedCrate, Ty, TyKind,
    TyVisitable, TypeDeclRef, TypeId, UIntTy,
};

/// The basic building blocks of symbolic layout information.
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum LayoutGuaranteeAtom {
    /// Symbolic size of type T, cf. `size_of<T>()`.
    SymSize(Ty),
    /// Symbolic alignment of type T, cf. `align_of<T>()`
    SymAlign(Ty),
    /// Concrete layout information as number of bytes.
    Concrete(#[drive(skip)] ByteCount),
    /// Target-specific default enum discriminant type for `#[repr(C)]`.
    /// See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.enum
    TargetDiscr,
}

impl LayoutGuaranteeAtom {
    pub fn mk_address_size() -> Self {
        Self::SymSize(Ty::mk_usize())
    }

    pub fn mk_address_size_for(
        translated: &TranslatedCrate,
        target: &TargetTriple,
    ) -> Option<Self> {
        translated
            .target_information
            .get(target)
            .map(|target_info| Self::Concrete(target_info.target_pointer_size))
    }

    pub fn make_primitive_align_for_target(
        ty: &LiteralTy,
        translated: &TranslatedCrate,
        target: &TargetTriple,
    ) -> Option<Self> {
        let target_info = translated.target_information.get(target)?;
        let align = match ty {
            LiteralTy::Int(int_ty) => match int_ty {
                IntTy::Isize => target_info.primitive_alignments.ptr_align,
                IntTy::I8 => target_info.primitive_alignments.i8_align,
                IntTy::I16 => target_info.primitive_alignments.i16_align,
                IntTy::I32 => target_info.primitive_alignments.i32_align,
                IntTy::I64 => target_info.primitive_alignments.i64_align,
                IntTy::I128 => target_info.primitive_alignments.i128_align,
            },
            LiteralTy::UInt(uint_ty) => match uint_ty {
                UIntTy::Usize => target_info.primitive_alignments.ptr_align,
                UIntTy::U8 => target_info.primitive_alignments.i8_align,
                UIntTy::U16 => target_info.primitive_alignments.i16_align,
                UIntTy::U32 => target_info.primitive_alignments.i32_align,
                UIntTy::U64 => target_info.primitive_alignments.i64_align,
                UIntTy::U128 => target_info.primitive_alignments.i128_align,
            },
            LiteralTy::Float(float_ty) => match float_ty {
                FloatTy::F16 => target_info.primitive_alignments.f16_align,
                FloatTy::F32 => target_info.primitive_alignments.f32_align,
                FloatTy::F64 => target_info.primitive_alignments.f64_align,
                FloatTy::F128 => target_info.primitive_alignments.f128_align,
            },
            LiteralTy::Bool => target_info.primitive_alignments.i8_align,
            LiteralTy::Char => target_info.primitive_alignments.i32_align, // FIXME: the target information in rustc doesn't mention chars?
        };
        Some(Self::Concrete(align))
    }
}

/// Composite symbolic layout expressions.
///
/// `non_exhaustive` since we might need many more composite layouts.
/// TODO: remove once we have all composite descriptions we need.
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[non_exhaustive]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum LayoutGuaranteeComp {
    /// A single symbolic layout atom.
    Atom(LayoutGuaranteeAtom),
    /// The sum of its atoms.
    Sum(Vec<LayoutGuaranteeComp>),
    /// An atom multiplied by a fixed scalar (e.g. `N` in [T;N]).
    Product {
        atom: Box<LayoutGuaranteeComp>,
        multiplier: ConstantExpr,
    },
    /// The next multiple of `target_align` from `base`.
    AlignedTo {
        base: Box<LayoutGuaranteeComp>,
        target_align: Box<LayoutGuaranteeComp>,
    },
    /// The maximum of these composite layout expressions.
    Max(Vec<LayoutGuaranteeComp>),
    /// For the packed representation, the overall and field alignments are each at most `max_align`.
    /// Thus, in contrast to the [`Self::Max`], we only need to compare a composition with a fixed
    /// constant atomic.
    Packed {
        max_align: LayoutGuaranteeAtom,
        to_pack: Box<LayoutGuaranteeComp>,
    },
}

impl LayoutGuaranteeComp {
    pub fn is_concrete(&self) -> Option<ByteCount> {
        match self {
            Self::Atom(LayoutGuaranteeAtom::Concrete(c)) => Some(*c),
            _ => None,
        }
    }

    pub fn realign(&mut self, align_to: Self) {
        match self {
            Self::AlignedTo { target_align, .. } => **target_align = align_to,
            Self::Atom(LayoutGuaranteeAtom::Concrete(c)) if align_to.is_concrete().is_some() => {
                let Some(align_to) = align_to.is_concrete() else {
                    unreachable!()
                };
                if !c.is_multiple_of(align_to) {
                    let aligned = *c + align_to - (*c % align_to);
                    *c = aligned;
                }
            }
            _ => {
                *self = Self::AlignedTo {
                    base: Box::new(self.clone()),
                    target_align: Box::new(align_to),
                }
            }
        }
    }

    pub fn max(&mut self, rhs: Self) {
        if let Self::Max(elems) = self {
            elems.push(rhs);
        } else {
            *self = Self::Max(vec![self.clone(), rhs]);
        }
    }
}

impl AddAssign for LayoutGuaranteeComp {
    fn add_assign(&mut self, rhs: LayoutGuaranteeComp) {
        if let Self::Sum(summands) = self {
            summands.push(rhs);
        } else {
            *self = Self::Sum(vec![self.clone(), rhs]);
        }
    }
}

/// Symbolic layout information about a type's size and alignment.
///
/// TODO: would it make sense to also have enum-specific information here?
/// E.g. whether the enum could have/has a guaranteed niche?
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)]
pub struct LayoutGuarantees {
    pub size: LayoutGuaranteeComp,
    pub alignment: LayoutGuaranteeComp,
}

impl LayoutGuarantees {
    pub const ONE_ZST: Self = Self {
        size: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(0)),
        alignment: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(1)),
    };

    pub fn mk_concrete(size: ByteCount, alignment: ByteCount) -> Self {
        if size.is_multiple_of(alignment) {
            Self {
                size: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(size)),
                alignment: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(alignment)),
            }
        } else {
            panic!(
                "Type size {} not a multiple of alignment {}!",
                size, alignment
            )
        }
    }

    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.array].
    pub fn mk_array(elem_ty: &Ty, elem_num: &ConstantExpr) -> Self {
        Self {
            size: LayoutGuaranteeComp::Product {
                atom: Box::new(LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymSize(
                    elem_ty.clone(),
                ))),
                multiplier: elem_num.clone(),
            },
            alignment: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymAlign(elem_ty.clone())),
        }
    }

    /// This is consistent with [`rustc_middle::ty::Ty::primitive_size`].
    ///
    /// However, currently it ignores potential inconsistencies with regard to
    /// [https://doc.rust-lang.org/reference/type-layout.html#r-layout.primitive.size].
    pub fn mk_primitive(primitive: &LiteralTy) -> Self {
        let size = match primitive {
            LiteralTy::Int(IntTy::Isize) | LiteralTy::UInt(UIntTy::Usize) => {
                return Self {
                    size: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::mk_address_size()),
                    alignment: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::mk_address_size()),
                };
            }
            LiteralTy::Int(int_ty) => int_ty.target_size(0),
            LiteralTy::UInt(uint_ty) => uint_ty.target_size(0),
            LiteralTy::Float(float_ty) => float_ty.target_size(),
            LiteralTy::Bool => 1,
            LiteralTy::Char => 4,
        };
        Self {
            size: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(size as ByteCount)),
            alignment: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymAlign(Ty::from(
                *primitive,
            ))),
        }
    }

    pub fn mk_symbolic(ty: Ty) -> Self {
        Self {
            size: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymSize(ty.clone())),
            alignment: LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymAlign(ty)),
        }
    }

    /// Computes the layout of a fixed, but unordered sequence of elements of the given types.
    /// This covers the Rust representation of both tuples and structs.
    pub fn mk_unordered_sequence<I>(tuple_elems: I) -> Self
    where
        I: Iterator<Item = Ty>,
    {
        let mut size_sum = Vec::new();
        let mut align_max = Vec::new();
        // Traverse the types in the tuple and add their information to the memoization database.
        for ty in tuple_elems {
            size_sum.push(LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymSize(
                ty.clone(),
            )));
            align_max.push(LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymAlign(ty)));
        }

        // An empty tuple is the unit type.
        // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.tuple.unit.
        if size_sum.is_empty() && align_max.is_empty() {
            return Self::ONE_ZST;
        }

        Self {
            // This implicitly follows from
            // https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout.struct
            size: LayoutGuaranteeComp::AlignedTo {
                base: Box::new(LayoutGuaranteeComp::Sum(size_sum)),
                target_align: Box::new(LayoutGuaranteeComp::Max(align_max.clone())),
            },
            // Technically, this is only the lower bound on the actual alignment.
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout, point 2.
            alignment: LayoutGuaranteeComp::Max(align_max),
        }
    }

    /// The layout of a pointer to `pointee`. Uses the symbolic size of meta-data.
    ///
    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.unsized].
    fn mk_ptr(pointee: &Ty, translated: &TranslatedCrate) -> Self {
        let meta = pointee.get_ptr_metadata(translated).into_type();
        let ptr_size = LayoutGuaranteeAtom::mk_address_size();
        let alignment = LayoutGuaranteeComp::Max(vec![
            LayoutGuaranteeComp::Atom(ptr_size.clone()),
            LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymSize(meta.clone())),
        ]);
        let size = LayoutGuaranteeComp::AlignedTo {
            base: Box::new(LayoutGuaranteeComp::Sum(vec![
                LayoutGuaranteeComp::Atom(ptr_size),
                LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymSize(meta)),
            ])),
            target_align: Box::new(alignment.clone()),
        };
        Self { size, alignment }
    }

    pub fn for_ty(ty: &Ty, translated: &TranslatedCrate) -> Option<Self> {
        match ty.kind() {
            // True Adt's (i.e. structs and enums) should have layout guarantees stored in
            // the corresponding type declaration.
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Adt(type_decl_id),
                generics,
            }) => {
                let op_poly = translated.type_decls.get(*type_decl_id)?.guarantees.clone();
                if let Some(poly_guarantees) = op_poly {
                    Some(poly_guarantees.substitute(generics))
                } else {
                    op_poly
                }
            }
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Tuple,
                generics,
            }) => Some(Self::mk_unordered_sequence(generics.types.iter().cloned())),
            TyKind::TypeVar(_) => Some(Self::mk_symbolic(ty.clone())),
            TyKind::Literal(literal_ty) => Some(Self::mk_primitive(literal_ty)),
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Box),
                generics,
            }) => Some(Self::mk_ptr(generics.types.first()?, translated)),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(Self::mk_ptr(ty, translated)),
            TyKind::FnPtr(_) => {
                let ptr_size = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::mk_address_size());
                Some(Self {
                    size: ptr_size.clone(),
                    alignment: ptr_size.clone(),
                })
            }
            TyKind::Array(elem_ty, elem_num) => Some(Self::mk_array(elem_ty, elem_num)),
            // For DSTs, we could think of a layout that is not only symbolic,
            // but also parametric in some meta data value.
            // For slice-like DSTs, we at least know that the alignment is the same as for the underlying array.
            //
            // See doc.rust-lang.org/reference/type-layout.html#r-layout.str
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Str),
                ..
            }) => {
                let mut base = Self::mk_symbolic(ty.clone());
                // Aligned to `u8`.
                base.alignment = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(1));
                Some(base)
            }
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.slice
            TyKind::Slice(elem_ty) => {
                let elem_layout = Self::for_ty(elem_ty, translated)?;
                let mut base = Self::mk_symbolic(ty.clone());
                base.alignment = elem_layout.alignment;
                Some(base)
            }
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.trait-object
            TyKind::DynTrait(_) => None,
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
/// A structure that computes and stores originally symbolic layouts, which have been
/// concretized as much as possible. Will not be used during translation.
pub struct Concretizer {
    computed_layouts: SeqHashMap<Ty, LayoutGuarantees>,
    curr_requested: HashSet<Ty>,
}

impl Concretizer {
    fn concretize_atom(
        &mut self,
        atom: &LayoutGuaranteeAtom,
        translated: &TranslatedCrate,
        target: Option<&TargetTriple>,
    ) -> LayoutGuaranteeComp {
        match atom {
            LayoutGuaranteeAtom::SymSize(ty) => {
                if ty == &Ty::mk_usize()
                    && let Some(target) = target
                    && let Some(target_specific_atom) =
                        LayoutGuaranteeAtom::mk_address_size_for(translated, target)
                {
                    LayoutGuaranteeComp::Atom(target_specific_atom)
                } else if let Some(layout) = self.concretized_layout_for(ty, translated, target) {
                    layout.size
                } else {
                    LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymSize(ty.clone()))
                }
            }
            LayoutGuaranteeAtom::SymAlign(ty) => {
                if let Some(literal_ty) = ty.as_literal()
                    && let Some(target) = target
                    && let Some(target_specific_atom) =
                        LayoutGuaranteeAtom::make_primitive_align_for_target(
                            literal_ty, translated, target,
                        )
                {
                    LayoutGuaranteeComp::Atom(target_specific_atom)
                } else if let Some(layout) = self.concretized_layout_for(ty, translated, target) {
                    layout.alignment
                } else {
                    LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::SymAlign(ty.clone()))
                }
            }
            LayoutGuaranteeAtom::Concrete(c) => {
                LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(*c))
            }
            LayoutGuaranteeAtom::TargetDiscr => {
                if let Some(target) = target
                    && let Some(info) = translated.target_information.get(target)
                {
                    LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(info.c_enum_min_size))
                } else {
                    LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::TargetDiscr)
                }
            }
        }
    }

    fn concretize_comp(
        &mut self,
        comp: &mut LayoutGuaranteeComp,
        translated: &TranslatedCrate,
        target: Option<&TargetTriple>,
    ) {
        match comp {
            LayoutGuaranteeComp::Atom(atom) => {
                *comp = self.concretize_atom(atom, translated, target);
            }
            LayoutGuaranteeComp::Sum(summands) => {
                let mut sum = Some(0);
                for summand in summands.iter_mut() {
                    self.concretize_comp(summand, translated, target);

                    if let Some(sum) = &mut sum
                        && let Some(c) = summand.is_concrete()
                    {
                        *sum += c;
                    } else {
                        sum = None;
                    }
                }
                if let Some(sum) = sum {
                    *comp = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(sum));
                }
            }
            LayoutGuaranteeComp::Product { atom, multiplier } => {
                self.concretize_comp(atom, translated, target);
                if let Some(c) = atom.is_concrete()
                    && let ConstantExprKind::Literal(Literal::Scalar(s)) = multiplier.kind
                {
                    // We assume that the scalar is never negative, since that wouldn't make any sense for the layout.
                    let result = match s {
                        ScalarValue::Unsigned(_, val) => val as u64 * c,
                        ScalarValue::Signed(_, val) => val as u128 as u64 * c,
                    };
                    *comp = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(result));
                }
            }
            LayoutGuaranteeComp::AlignedTo { base, target_align } => {
                self.concretize_comp(base, translated, target);
                self.concretize_comp(target_align, translated, target);
                if let Some(c1) = base.is_concrete()
                    && let Some(c2) = target_align.is_concrete()
                {
                    if c1.is_multiple_of(c2) {
                        *comp = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(c1));
                    } else {
                        let aligned = c1 + c2 - (c1 % c2);
                        *comp = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(aligned));
                    }
                }
            }
            LayoutGuaranteeComp::Max(max_contenders) => {
                let mut max = Some(0);
                for contender in max_contenders.iter_mut() {
                    self.concretize_comp(contender, translated, target);

                    if let Some(max) = &mut max
                        && let Some(c) = contender.is_concrete()
                    {
                        *max = u64::max(*max, c);
                    } else {
                        max = None;
                    }
                }
                if let Some(max) = max {
                    *comp = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(max));
                }
            }
            LayoutGuaranteeComp::Packed { max_align, to_pack } => {
                self.concretize_atom(max_align, translated, target);
                self.concretize_comp(to_pack, translated, target);
                if let LayoutGuaranteeAtom::Concrete(c1) = max_align
                    && let Some(c2) = to_pack.is_concrete()
                {
                    if *c1 < c2 {
                        *comp = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(*c1));
                    } else {
                        *comp = LayoutGuaranteeComp::Atom(LayoutGuaranteeAtom::Concrete(c2));
                    }
                }
            }
        }
    }

    /// Computes or looks up a concretized layout for the given type.
    ///
    /// This will concretize the layout as much as possible, but might still
    /// return a (partially) symbolic layout.
    pub fn concretized_layout_for(
        &mut self,
        ty: &Ty,
        translated: &TranslatedCrate,
        target: Option<&TargetTriple>,
    ) -> Option<LayoutGuarantees> {
        if let Some(layout) = self.computed_layouts.get(ty) {
            Some(layout.clone())
        } else if self.curr_requested.contains(ty) {
            // In case of recursive/inductive layout constraints,
            // stop computation for that branch.
            None
        } else {
            let mut symbolic_layout = LayoutGuarantees::for_ty(ty, translated)?;
            self.curr_requested.insert(ty.clone());

            self.concretize_comp(&mut symbolic_layout.size, translated, target);
            self.concretize_comp(&mut symbolic_layout.alignment, translated, target);

            self.curr_requested.remove(ty);
            Some(symbolic_layout)
        }
    }
}
