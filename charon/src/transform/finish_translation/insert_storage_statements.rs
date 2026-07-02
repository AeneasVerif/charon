//! Add missing storage markers -- in MIR, some locals are considered "always" initialised, and have
//! no StorageLive and StorageDead instructions associated; this always includes the arguments
//! and the return local, but also sometimes includes other locals. We make sure these additional
//! locals get initialised at the start of the function and deallocated before function exits if
//! they're used anywhere.
use derive_generic_visitor::Visitor;

use crate::ast::*;
use crate::ids::IndexVec;
use crate::transform::TransformCtx;
use crate::transform::ctx::{TransformPass, UllbcPass};
use crate::ullbc_ast::{BlockId, TerminatorKind};

#[derive(Visitor)]
struct StorageVisitor {
    local_status: IndexVec<LocalId, LocalStatus>,
}

struct LocalStatus {
    used: bool,
    has_storage_live: bool,
    has_storage_dead: bool,
}

impl StorageVisitor {
    fn new(locals: &Locals) -> Self {
        let local_status = locals.locals.map_ref(|local| {
            let is_return = local.index == LocalId::ZERO;
            let is_argument = !is_return && locals.is_return_or_arg(local.index);
            LocalStatus {
                used: is_return || is_argument,
                has_storage_live: is_argument,
                has_storage_dead: is_return,
            }
        });
        Self { local_status }
    }

    fn locals_missing_storage_lives(&self) -> Vec<LocalId> {
        self.local_status
            .iter_enumerated()
            .filter(|(_, status)| status.used && !status.has_storage_live)
            .map(|(local, _)| local)
            .collect()
    }

    fn locals_missing_storage_deads(&self) -> Vec<LocalId> {
        self.local_status
            .iter_enumerated()
            .filter(|(_, status)| status.used && !status.has_storage_dead)
            .map(|(local, _)| local)
            .collect()
    }
}

impl VisitBody for StorageVisitor {
    fn visit_locals(&mut self, _: &Locals) -> ::std::ops::ControlFlow<Self::Break> {
        // Don't look inside the local declarations otherwise we'll think they're all used.
        ControlFlow::Continue(())
    }
    fn enter_local_id(&mut self, lid: &LocalId) {
        self.local_status[*lid].used = true;
    }
    fn enter_llbc_statement(&mut self, st: &llbc_ast::Statement) {
        match &st.kind {
            llbc_ast::StatementKind::StorageLive(lid) => {
                self.local_status[*lid].has_storage_live = true;
            }
            llbc_ast::StatementKind::StorageDead(lid) => {
                self.local_status[*lid].has_storage_dead = true;
            }
            _ => {}
        }
    }
    fn enter_ullbc_statement(&mut self, st: &ullbc_ast::Statement) {
        match &st.kind {
            ullbc_ast::StatementKind::StorageLive(lid) => {
                self.local_status[*lid].has_storage_live = true;
            }
            ullbc_ast::StatementKind::StorageDead(lid) => {
                self.local_status[*lid].has_storage_dead = true;
            }
            _ => {}
        }
    }
}

pub struct Transform;
impl Transform {
    fn transform_ullbc_body(
        &self,
        body: &mut ullbc_ast::ExprBody,
        insert_missing_storage_deads: bool,
    ) {
        let mut storage_visitor = StorageVisitor::new(&body.locals);
        let _ = storage_visitor.visit(body);

        // Insert StorageLive instructions for the always initialised locals.
        let locals_with_missing_storage_lives = storage_visitor.locals_missing_storage_lives();
        let first_block = body.body.get_mut(BlockId::ZERO).unwrap();
        let first_span = if let Some(fst) = first_block.statements.first() {
            fst.span
        } else {
            first_block.terminator.span
        };
        let new_statements = locals_with_missing_storage_lives.iter().map(|local| {
            ullbc_ast::Statement::new(first_span, ullbc_ast::StatementKind::StorageLive(*local))
        });
        first_block.statements.splice(0..0, new_statements);

        // Insert StorageDead instructions before every function exit.
        if insert_missing_storage_deads {
            let locals_with_missing_storage_deads = storage_visitor.locals_missing_storage_deads();
            for block in &mut body.body {
                if matches!(
                    block.terminator.kind,
                    TerminatorKind::Abort(_)
                        | TerminatorKind::Return
                        | TerminatorKind::UnwindResume
                ) {
                    let span = block.terminator.span;
                    block
                        .statements
                        .extend(locals_with_missing_storage_deads.iter().rev().map(|local| {
                            ullbc_ast::Statement::new(
                                span,
                                ullbc_ast::StatementKind::StorageDead(*local),
                            )
                        }));
                }
            }
        }
    }

    fn transform_llbc_body(
        &self,
        body: &mut llbc_ast::ExprBody,
        insert_missing_storage_deads: bool,
    ) {
        let mut storage_visitor = StorageVisitor::new(&body.locals);
        let _ = storage_visitor.visit(body);

        let locals_with_missing_storage_lives = storage_visitor.locals_missing_storage_lives();
        let first_span = if let Some(fst) = body.body.statements.first() {
            fst.span
        } else {
            body.span
        };
        let new_statements = locals_with_missing_storage_lives.iter().map(|local| {
            llbc_ast::Statement::new(first_span, llbc_ast::StatementKind::StorageLive(*local))
        });
        body.body.statements.splice(0..0, new_statements);

        if insert_missing_storage_deads {
            let locals_with_missing_storage_deads = storage_visitor.locals_missing_storage_deads();
            body.body.transform_sequences(|statements| {
                if !matches!(
                    &statements[0].kind,
                    llbc_ast::StatementKind::Abort(_) | llbc_ast::StatementKind::Return
                ) {
                    return Vec::new();
                }
                let span = statements[0].span;
                locals_with_missing_storage_deads
                    .iter()
                    .rev()
                    .map(|local| {
                        llbc_ast::Statement::new(span, llbc_ast::StatementKind::StorageDead(*local))
                    })
                    .collect()
            });
        }
    }

    fn transform_function(&self, fun: &mut FunDecl) {
        // Don't insert `StorageDead`s inside global initializers because the locals there are
        // actually statics.
        let insert_missing_storage_deads = fun.is_global_initializer.is_none();
        match &mut fun.body {
            Body::Unstructured(body) => {
                self.transform_ullbc_body(body, insert_missing_storage_deads)
            }
            Body::Structured(body) => self.transform_llbc_body(body, insert_missing_storage_deads),
            _ => {}
        }
    }
}

impl UllbcPass for Transform {
    fn transform_function(&self, _ctx: &mut TransformCtx, fun: &mut FunDecl) {
        self.transform_function(fun)
    }
}

impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|_ctx, fun| self.transform_function(fun));
    }
}
