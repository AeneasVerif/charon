//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::ullbc_ast::*;
use itertools::Itertools;

impl ItemTransCtx<'_, '_> {
    /// Generate a fake function body for ADT constructors.
    pub(crate) fn build_ctor_body(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<Body, Error> {
        let hax::FullDefKind::Ctor {
            adt_def_id,
            ctor_of,
            variant_id,
            fields,
            output_ty,
        } = def.kind()
        else {
            unreachable!()
        };
        let tref = self
            .translate_type_decl_ref(span, &def.this().with_def_id(self.hax_state(), adt_def_id))?;
        let output_ty = self.translate_ty(span, output_ty)?;
        let mut locals = Locals::new(fields.len());
        locals.new_var(None, output_ty);
        let args: Vec<_> = fields
            .iter()
            .map(|field| -> Result<Operand, Error> {
                let ty = self.translate_ty(span, &field.ty)?;
                let place = locals.new_var(None, ty);
                Ok(Operand::Move(place))
            })
            .try_collect()?;
        let variant = match ctor_of {
            hax::CtorOf::Struct => None,
            hax::CtorOf::Variant => Some(VariantId::from(*variant_id)),
        };
        let st_kind = StatementKind::Assign(
            locals.return_place(),
            Rvalue::Aggregate(AggregateKind::Adt(tref, variant, None), args),
        );
        let statement = Statement::new(span, st_kind);
        let block = BlockData {
            statements: vec![statement],
            terminator: Terminator::new(span, TerminatorKind::Return),
        };
        let body = Body::Unstructured(GExprBody {
            span,
            locals,
            comments: Default::default(),
            body: [block].into_iter().collect(),
        });
        Ok(body)
    }

    /// Checks whether the given id corresponds to a built-in type.
    pub(crate) fn recognize_builtin_fun(
        &mut self,
        item: &hax::ItemRef,
    ) -> Result<Option<BuiltinFunId>, Error> {
        let def = self.hax_def(item)?;
        let fun_id =
            if def.diagnostic_item.as_deref() == Some("box_new") && !self.t_ctx.options.raw_boxes {
                Some(BuiltinFunId::BoxNew)
            } else {
                None
            };
        Ok(fun_id)
    }
}
