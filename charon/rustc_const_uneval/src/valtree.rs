//! Reading type-system constants (valtrees).
use crate::*;

impl<'tcx> ConstReader<'tcx> {
    /// Read a type-system constant back into a structured constant.
    pub(crate) fn read_valtree(
        &self,
        span: rustc_span::Span,
        value: ty::Value<'tcx>,
    ) -> Result<Const<'tcx>, ReadError<'tcx>> {
        let tcx = self.tcx;
        let valtree = value.valtree;
        // E.g. the types of the fields of a destructured ADT aren't normalized.
        let mut ty = self.normalize(value.ty);
        // Reveal opaque types.
        if let ty::Alias(_, alias) = ty.kind()
            && let ty::AliasTyKind::Opaque { def_id } = alias.kind
        {
            let hidden_ty = tcx.type_of(def_id).instantiate(tcx, alias.args);
            ty = self.normalize(hidden_ty.skip_normalization());
        }
        let read_at = |ty, valtree| self.read_valtree(span, ty::Value { ty, valtree });
        let read_field = |field: ty::Const<'tcx>| self.read_valtree(span, field.to_value());

        let kind = match (&*valtree, ty.kind()) {
            // Unlike in const-eval memory, we read the value of a pattern type at its base type.
            (_, ty::Pat(inner_ty, _)) => return read_at(*inner_ty, valtree),
            (ty::ValTreeKind::Branch(fields), ty::Ref(_, inner_ty, _))
                if let ty::Slice(_) | ty::Str = inner_ty.kind() =>
            {
                let len = fields.len() as u64;
                // The array the pointee was unsized from.
                let array_ty = Ty::new_array(tcx, inner_ty.sequence_element_type(tcx), len);
                // We read slices at that array type, but `str`s as themselves.
                let pointee_ty = match inner_ty.kind() {
                    ty::Slice(_) => array_ty,
                    _ => *inner_ty,
                };
                ConstKind::Ptr {
                    target: PtrTarget::Inline(Box::new(read_at(pointee_ty, valtree)?)),
                    unsize: Some(Unsize {
                        from: array_ty,
                        to: *inner_ty,
                    }),
                }
            }
            // For other unsized pointees, computing the metadata requires putting them in an
            // allocation.
            (_, ty::Ref(_, inner_ty, _)) if !inner_ty.is_sized(tcx, self.typing_env) => {
                let val = tcx.valtree_to_const_val(ty::Value { ty, valtree });
                return self.read_const_value(span, val, ty, ReadMode::Structured);
            }
            (_, ty::Ref(_, inner_ty, _)) => ConstKind::Ptr {
                target: PtrTarget::Inline(Box::new(read_at(*inner_ty, valtree)?)),
                unsize: None,
            },
            (ty::ValTreeKind::Branch(fields), ty::Str) => {
                let bytes = fields
                    .iter()
                    .map(|field| {
                        let leaf = field.try_to_leaf();
                        leaf.expect("the valtree of a `str` should be a list of leaves")
                            .to_u8()
                    })
                    .collect();
                ConstKind::str(bytes)
            }
            (ty::ValTreeKind::Branch(fields), ty::Array(..) | ty::Slice(..) | ty::Tuple(..)) => {
                ConstKind::Aggregate {
                    variant: None,
                    fields: fields.iter().map(read_field).collect::<Result<_, _>>()?,
                }
            }
            (ty::ValTreeKind::Branch(_), ty::Adt(..)) => {
                let contents = ty::Value { valtree, ty }.destructure_adt_const();
                let fields = contents.fields.iter().copied().map(read_field);
                ConstKind::Aggregate {
                    variant: Some(contents.variant),
                    fields: fields.collect::<Result<_, _>>()?,
                }
            }
            (ty::ValTreeKind::Branch(fields), ty::FnDef(..)) if fields.is_empty() => {
                ConstKind::fn_def(tcx, ty)
            }
            (ty::ValTreeKind::Leaf(x), ty::RawPtr(..)) => {
                ConstKind::PtrNoProvenance(x.to_bits_unchecked())
            }
            (ty::ValTreeKind::Leaf(x), _) => ConstKind::Scalar(*x),
            _ => panic!("unexpected valtree {valtree:?} of type {ty:?}"),
        };
        Ok(Const { ty, kind })
    }
}
