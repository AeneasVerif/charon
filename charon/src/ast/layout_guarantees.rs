use std::{
    collections::{HashMap, HashSet},
    ops::AddAssign,
};

use derive_generic_visitor::{Drive, DriveMut};
use serde_state::{DeserializeState, SerializeState};

use crate::ast::{
    BuiltinTy, ConcreteByteCount, ConstantExpr, ConstantExprKind, FloatTy, HashConsSerializerState,
    IntTy, Literal, LiteralTy, ScalarValue, TargetTriple, TranslatedCrate, Ty, TyKind, TyVisitable,
    TypeDeclRef, TypeId, UIntTy,
};

/// The basic building blocks of symbolic layout information.
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum BasicByteCount {
    /// Symbolic size of type T, cf. `size_of<T>()`.
    SymSize(Ty),
    /// Symbolic alignment of type T, cf. `align_of<T>()`
    SymAlign(Ty),
    /// Concrete layout information as number of bytes.
    Concrete(#[drive(skip)] ConcreteByteCount),
    /// Target-specific default enum discriminant type for `#[repr(C)]`.
    /// See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.enum
    TargetDiscr,
}

impl BasicByteCount {
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
#[derive(Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut)]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum SymbolicByteCount {
    /// A single symbolic layout atom.
    Atom(BasicByteCount),
    /// The sum of its atoms.
    Sum(Vec<SymbolicByteCount>),
    /// An atom multiplied by a fixed scalar (e.g. `N` in [T;N]).
    Product {
        atom: Box<SymbolicByteCount>,
        multiplier: ConstantExpr,
    },
    /// The next multiple of `target_align` from `base`.
    AlignedTo {
        base: Box<SymbolicByteCount>,
        target_align: Box<SymbolicByteCount>,
    },
    /// The maximum of these composite layout expressions.
    Max(Vec<SymbolicByteCount>),
    /// For the packed representation, the overall and field alignments are each at most `max_align`.
    /// Thus, in contrast to the [`Self::Max`], we only need to compare a composition with a fixed
    /// constant atomic.
    Packed {
        max_align: BasicByteCount,
        to_pack: Box<SymbolicByteCount>,
    },
}

impl Default for SymbolicByteCount {
    fn default() -> Self {
        Self::Atom(BasicByteCount::Concrete(0))
    }
}

impl SymbolicByteCount {
    pub fn is_concrete(&self) -> Option<ConcreteByteCount> {
        match self {
            Self::Atom(BasicByteCount::Concrete(c)) => Some(*c),
            _ => None,
        }
    }

    pub fn realign(&mut self, align_to: Self) {
        match self {
            Self::AlignedTo { target_align, .. } => **target_align = align_to,
            Self::Atom(BasicByteCount::Concrete(c)) if align_to.is_concrete().is_some() => {
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
            if let Self::Max(rhs_max) = rhs {
                elems.extend(rhs_max);
            } else {
                elems.push(rhs);
            }
        } else {
            *self = Self::Max(vec![self.clone(), rhs]);
        }
    }
}

impl AddAssign for SymbolicByteCount {
    fn add_assign(&mut self, rhs: SymbolicByteCount) {
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
    pub size: SymbolicByteCount,
    pub alignment: SymbolicByteCount,
}

impl LayoutGuarantees {
    pub const ONE_ZST: Self = Self {
        size: SymbolicByteCount::Atom(BasicByteCount::Concrete(0)),
        alignment: SymbolicByteCount::Atom(BasicByteCount::Concrete(1)),
    };

    pub fn mk_concrete(size: ConcreteByteCount, alignment: ConcreteByteCount) -> Self {
        if size.is_multiple_of(alignment) {
            Self {
                size: SymbolicByteCount::Atom(BasicByteCount::Concrete(size)),
                alignment: SymbolicByteCount::Atom(BasicByteCount::Concrete(alignment)),
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
            size: SymbolicByteCount::Product {
                atom: Box::new(SymbolicByteCount::Atom(BasicByteCount::SymSize(
                    elem_ty.clone(),
                ))),
                multiplier: elem_num.clone(),
            },
            alignment: SymbolicByteCount::Atom(BasicByteCount::SymAlign(elem_ty.clone())),
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
                    size: SymbolicByteCount::Atom(BasicByteCount::mk_address_size()),
                    alignment: SymbolicByteCount::Atom(BasicByteCount::mk_address_size()),
                };
            }
            LiteralTy::Int(int_ty) => int_ty.target_size(0),
            LiteralTy::UInt(uint_ty) => uint_ty.target_size(0),
            LiteralTy::Float(float_ty) => float_ty.target_size(),
            LiteralTy::Bool => 1,
            LiteralTy::Char => 4,
        };
        Self {
            size: SymbolicByteCount::Atom(BasicByteCount::Concrete(size as ConcreteByteCount)),
            alignment: SymbolicByteCount::Atom(BasicByteCount::SymAlign(Ty::from(*primitive))),
        }
    }

    pub fn mk_symbolic(ty: Ty) -> Self {
        Self {
            size: SymbolicByteCount::Atom(BasicByteCount::SymSize(ty.clone())),
            alignment: SymbolicByteCount::Atom(BasicByteCount::SymAlign(ty)),
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
            size_sum.push(SymbolicByteCount::Atom(BasicByteCount::SymSize(ty.clone())));
            align_max.push(SymbolicByteCount::Atom(BasicByteCount::SymAlign(ty)));
        }

        // An empty tuple is the unit type.
        // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.tuple.unit.
        if size_sum.is_empty() && align_max.is_empty() {
            return Self::ONE_ZST;
        }

        Self {
            // This implicitly follows from
            // https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout.struct
            size: SymbolicByteCount::AlignedTo {
                base: Box::new(SymbolicByteCount::Sum(size_sum)),
                target_align: Box::new(SymbolicByteCount::Max(align_max.clone())),
            },
            // Technically, this is only the lower bound on the actual alignment.
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout, point 2.
            alignment: SymbolicByteCount::Max(align_max),
        }
    }

    /// Computes the layout of a fixed sequence of elements of the given types as guaranteed by [`repr(C)`].
    /// Based on https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.struct.size-field-offset
    pub fn mk_ordered_sequence_repr_c<I>(fields: I, prefix_tag_layout: Option<Self>) -> Self
    where
        I: Iterator<Item = Ty>,
    {
        let mut align_max = Vec::new();
        let mut curr_offset = if let Some(tag_guarantees) = prefix_tag_layout {
            align_max.push(tag_guarantees.alignment);
            tag_guarantees.size
        } else {
            SymbolicByteCount::Atom(BasicByteCount::Concrete(0))
        };

        for ty in fields {
            let field_size = SymbolicByteCount::Atom(BasicByteCount::SymSize(ty.clone()));
            let field_align = SymbolicByteCount::Atom(BasicByteCount::SymAlign(ty));

            let field_offset = SymbolicByteCount::AlignedTo {
                base: Box::new(curr_offset.clone()),
                target_align: Box::new(field_align.clone()),
            };
            align_max.push(field_align);
            curr_offset = field_offset;
            curr_offset += field_size;
        }

        Self {
            size: SymbolicByteCount::AlignedTo {
                base: Box::new(curr_offset),
                target_align: Box::new(SymbolicByteCount::Max(align_max.clone())),
            },
            alignment: SymbolicByteCount::Max(align_max),
        }
    }

    pub fn mk_tagged_union<V, F>(
        variants: V,
        discr_layout_guarantee: Option<Self>,
        translated: &TranslatedCrate,
        is_union: bool,
    ) -> Self
    where
        V: Iterator<Item = F>,
        F: Iterator<Item = Ty>,
    {
        let mut max_size = SymbolicByteCount::Max(Vec::new());
        let mut max_align = SymbolicByteCount::Max(Vec::new());

        for mut fields in variants {
            // Unions don't have an actual structure, but a single field, which needs to be
            // handled as if it has the same repr annotation as the whole union.
            let variant_guarantees = if is_union {
                Self::for_ty_inner(&fields.next().unwrap(), translated, true).unwrap()
            } else {
                LayoutGuarantees::mk_ordered_sequence_repr_c(fields, discr_layout_guarantee.clone())
            };
            max_size.max(variant_guarantees.size);
            max_align.max(variant_guarantees.alignment);
        }

        let size = SymbolicByteCount::AlignedTo {
            base: Box::new(max_size),
            target_align: Box::new(max_align.clone()),
        };
        LayoutGuarantees {
            size,
            alignment: max_align,
        }
    }

    /// The layout of a pointer to `pointee`. Uses the symbolic size of meta-data.
    ///
    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.unsized].
    fn mk_ptr(pointee: &Ty, translated: &TranslatedCrate) -> Self {
        let meta = pointee.get_ptr_metadata(translated).into_type();
        let ptr_size = BasicByteCount::mk_address_size();
        let alignment = SymbolicByteCount::Max(vec![
            SymbolicByteCount::Atom(ptr_size.clone()),
            SymbolicByteCount::Atom(BasicByteCount::SymSize(meta.clone())),
        ]);
        let size = SymbolicByteCount::AlignedTo {
            base: Box::new(SymbolicByteCount::Sum(vec![
                SymbolicByteCount::Atom(ptr_size),
                SymbolicByteCount::Atom(BasicByteCount::SymSize(meta)),
            ])),
            target_align: Box::new(alignment.clone()),
        };
        Self { size, alignment }
    }

    fn for_ty_inner(ty: &Ty, translated: &TranslatedCrate, force_repr_c: bool) -> Option<Self> {
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
            }) => {
                if force_repr_c {
                    Some(Self::mk_ordered_sequence_repr_c(
                        generics.types.iter().cloned(),
                        None,
                    ))
                } else {
                    Some(Self::mk_unordered_sequence(generics.types.iter().cloned()))
                }
            }
            TyKind::TypeVar(_) => Some(Self::mk_symbolic(ty.clone())),
            TyKind::Literal(literal_ty) => Some(Self::mk_primitive(literal_ty)),
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Box),
                generics,
            }) => Some(Self::mk_ptr(generics.types.first()?, translated)),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(Self::mk_ptr(ty, translated)),
            TyKind::FnPtr(_) => {
                let ptr_size = SymbolicByteCount::Atom(BasicByteCount::mk_address_size());
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
                base.alignment = SymbolicByteCount::Atom(BasicByteCount::Concrete(1));
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

    pub fn for_ty(ty: &Ty, translated: &TranslatedCrate) -> Option<Self> {
        Self::for_ty_inner(ty, translated, false)
    }

    pub fn is_concrete(&self) -> Option<(ConcreteByteCount, ConcreteByteCount)> {
        self.size.is_concrete().zip(self.alignment.is_concrete())
    }
}

/// A structure that computes and stores originally symbolic layouts, which have been
/// normalized for a given target as much as possible. Will not be used during translation.
pub struct LayoutComputer<'a> {
    krate: &'a TranslatedCrate,
    target: Option<&'a TargetTriple>,
    cache: HashMap<Ty, LayoutGuarantees>,
    /// Set to bail on cycles in the computation.
    stack: HashSet<Ty>,
}
impl<'a> LayoutComputer<'a> {
    pub fn new(krate: &'a TranslatedCrate, target: Option<&'a TargetTriple>) -> Self {
        Self {
            krate,
            target,
            cache: HashMap::new(),
            stack: HashSet::new(),
        }
    }

    fn normalize_atom(&mut self, atom: &BasicByteCount) -> SymbolicByteCount {
        match atom {
            BasicByteCount::SymSize(ty) => {
                if ty == &Ty::mk_usize()
                    && let Some(target) = self.target
                    && let Some(target_specific_atom) =
                        BasicByteCount::mk_address_size_for(self.krate, target)
                {
                    SymbolicByteCount::Atom(target_specific_atom)
                } else if let Some(layout) = self.compute_layout(ty.clone()) {
                    layout.size
                } else {
                    SymbolicByteCount::Atom(BasicByteCount::SymSize(ty.clone()))
                }
            }
            BasicByteCount::SymAlign(ty) => {
                if let Some(literal_ty) = ty.as_literal()
                    && let Some(target) = self.target
                    && let Some(target_specific_atom) =
                        BasicByteCount::make_primitive_align_for_target(
                            literal_ty, self.krate, target,
                        )
                {
                    SymbolicByteCount::Atom(target_specific_atom)
                } else if let Some(layout) = self.compute_layout(ty.clone()) {
                    layout.alignment
                } else {
                    SymbolicByteCount::Atom(BasicByteCount::SymAlign(ty.clone()))
                }
            }
            BasicByteCount::Concrete(c) => SymbolicByteCount::Atom(BasicByteCount::Concrete(*c)),
            BasicByteCount::TargetDiscr => {
                if let Some(target) = self.target
                    && let Some(info) = self.krate.target_information.get(target)
                {
                    SymbolicByteCount::Atom(BasicByteCount::Concrete(info.c_enum_min_size))
                } else {
                    SymbolicByteCount::Atom(BasicByteCount::TargetDiscr)
                }
            }
        }
    }

    fn normalize_symbolic_byte_count(&mut self, sym_byte_count: &mut SymbolicByteCount) {
        match sym_byte_count {
            SymbolicByteCount::Atom(atom) => {
                *sym_byte_count = self.normalize_atom(atom);
            }
            SymbolicByteCount::Sum(summands) => {
                let mut sum = Some(0);
                for summand in summands.iter_mut() {
                    self.normalize_symbolic_byte_count(summand);

                    if let Some(sum) = &mut sum
                        && let Some(c) = summand.is_concrete()
                    {
                        *sum += c;
                    } else {
                        sum = None;
                    }
                }
                if let Some(sum) = sum {
                    *sym_byte_count = SymbolicByteCount::Atom(BasicByteCount::Concrete(sum));
                }
            }
            SymbolicByteCount::Product { atom, multiplier } => {
                self.normalize_symbolic_byte_count(atom);
                if let Some(c) = atom.is_concrete()
                    && let ConstantExprKind::Literal(Literal::Scalar(s)) = multiplier.kind
                {
                    // We assume that the scalar is never negative, since that wouldn't make any sense for the layout.
                    let result = match s {
                        ScalarValue::Unsigned(_, val) => val as u64 * c,
                        ScalarValue::Signed(_, val) => val as u128 as u64 * c,
                    };
                    *sym_byte_count = SymbolicByteCount::Atom(BasicByteCount::Concrete(result));
                }
            }
            SymbolicByteCount::AlignedTo { base, target_align } => {
                self.normalize_symbolic_byte_count(base);
                self.normalize_symbolic_byte_count(target_align);
                if let Some(c1) = base.is_concrete()
                    && let Some(c2) = target_align.is_concrete()
                {
                    if c1.is_multiple_of(c2) {
                        *sym_byte_count = SymbolicByteCount::Atom(BasicByteCount::Concrete(c1));
                    } else {
                        let aligned = c1 + c2 - (c1 % c2);
                        *sym_byte_count =
                            SymbolicByteCount::Atom(BasicByteCount::Concrete(aligned));
                    }
                }
            }
            SymbolicByteCount::Max(max_contenders) => {
                let mut max = Some(0);
                for contender in max_contenders.iter_mut() {
                    self.normalize_symbolic_byte_count(contender);

                    if let Some(max) = &mut max
                        && let Some(c) = contender.is_concrete()
                    {
                        *max = u64::max(*max, c);
                    } else {
                        max = None;
                    }
                }
                if let Some(max) = max {
                    *sym_byte_count = SymbolicByteCount::Atom(BasicByteCount::Concrete(max));
                }
            }
            SymbolicByteCount::Packed { max_align, to_pack } => {
                self.normalize_atom(max_align);
                self.normalize_symbolic_byte_count(to_pack);
                if let BasicByteCount::Concrete(c1) = max_align
                    && let Some(c2) = to_pack.is_concrete()
                {
                    if *c1 < c2 {
                        *sym_byte_count = SymbolicByteCount::Atom(BasicByteCount::Concrete(*c1));
                    } else {
                        *sym_byte_count = SymbolicByteCount::Atom(BasicByteCount::Concrete(c2));
                    }
                }
            }
        }
    }

    /// Computes the most precise layout guarantees we can deduce for this type.
    pub fn compute_layout(&mut self, ty: Ty) -> Option<LayoutGuarantees> {
        if let Some(layout) = self.cache.get(&ty) {
            Some(layout.clone())
        } else if self.stack.contains(&ty) {
            // In case of recursive/inductive layout constraints,
            // stop computation for that branch.
            None
        } else {
            let mut symbolic_layout = LayoutGuarantees::for_ty(&ty, self.krate)?;
            self.stack.insert(ty.clone());

            self.normalize_symbolic_byte_count(&mut symbolic_layout.size);
            self.normalize_symbolic_byte_count(&mut symbolic_layout.alignment);

            self.stack.remove(&ty);
            self.cache.insert(ty, symbolic_layout.clone());
            Some(symbolic_layout)
        }
    }
}
