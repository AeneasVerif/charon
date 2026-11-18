//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use crate::name_matcher::NamePattern;
use crate::transform::ctx::UllbcPass;
use crate::transform::{CowBox, TransformCtx};
use crate::ullbc_ast::*;

pub struct Transform {
    unreachable: Option<Call>,
}

impl Transform {
    pub fn new(ctx: &TransformCtx) -> CowBox<dyn UllbcPass> {
        let unreachable_pattern = NamePattern::parse("core::hint::unreachable_unchecked").unwrap();
        let unreachable = ctx
            .translated
            .fun_decls
            .iter_indexed()
            .find(|(_, decl)| unreachable_pattern.matches(&ctx.translated, &decl.item_meta.name))
            .map(|(id, _)| Call {
                func: FnOperand::Regular(FnPtr::new(FnPtrKind::Fun(id), GenericArgs::empty())),
                args: vec![],
                safety: CallSafety::Inherit,
            });
        CowBox::Owned(Box::new(Self { unreachable }))
    }
}

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.reconstruct_asserts
    }

    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        let Some(unreachable) = &self.unreachable else {
            return;
        };
        // Start by computing the set of blocks which are actually panics.
        // Remark: doing this in two steps because reading the blocks at random
        // while doing in-place updates is not natural to do in Rust.
        let panics = b.as_abort_map();

        for block in b.body.iter_mut() {
            if let TerminatorKind::Switch { data, branches } = &block.terminator.kind
                && let Some((true_id, false_id)) = data.as_if()
                && let SwitchScrutinee::Value(discr) = data.scrutinee.clone()
            {
                let (true_bid, false_bid) = (branches[true_id], branches[false_id]);
                let (nbid, expected, (abort, call)) = if let Some(abort) = panics.get(&true_bid) {
                    (false_bid, false, abort)
                } else if let Some(abort) = panics.get(&false_bid) {
                    (true_bid, true, abort)
                } else {
                    continue;
                };

                let call = match abort {
                    AbortKind::Panic | AbortKind::UnwindTerminate(..) => call
                        .clone()
                        .expect("panics and unwind terminates always have a call"),
                    AbortKind::UndefinedBehavior => unreachable.clone(),
                };
                let _ = std::mem::replace(
                    &mut block.terminator.kind,
                    TerminatorKind::Goto { target: nbid },
                );
                block.statements.push(Statement::new(
                    block.terminator.span,
                    StatementKind::Assert {
                        assert: Assert {
                            cond: discr,
                            expected,
                            check_kind: None,
                            call: Box::new(call),
                        },
                        on_failure: abort.clone(),
                    },
                ));
            }
        }
    }
}
