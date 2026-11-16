//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use crate::ast::from_rustc::LangItem;
use crate::name_matcher::NamePattern;
use crate::transform::ctx::UllbcPass;
use crate::transform::{CowBox, TransformCtx};
use crate::ullbc_ast::*;

/// The calls to emit for the asserts we reconstruct
struct AssertFailureCalls {
    assume: Call,
    cannot_unwind: Call,
    in_cleanup: Call,
}

pub struct Transform {
    calls: Option<AssertFailureCalls>,
}

impl Transform {
    pub fn new(ctx: &TransformCtx) -> CowBox<dyn UllbcPass> {
        let assume_pattern = NamePattern::parse("core::intrinsics::assume").unwrap();
        let (mut assume, mut cannot_unwind, mut in_cleanup) = (None, None, None);
        for (id, decl) in ctx.translated.fun_decls.iter_indexed() {
            let mut args = vec![];
            let slot = match decl.item_meta.lang_item {
                Some(LangItem::PanicCannotUnwind) => &mut cannot_unwind,
                Some(LangItem::PanicInCleanup) => &mut in_cleanup,
                None if assume_pattern.matches(&ctx.translated, &decl.item_meta.name) => {
                    args.push(Operand::Const(ConstantExpr::mk_bool(false)));
                    &mut assume
                }
                _ => continue,
            };
            *slot = Some(Call {
                func: FnOperand::Regular(FnPtr::new(FnPtrKind::Fun(id), GenericArgs::empty())),
                args,
                safety: CallSafety::Inherit,
            });
        }
        let calls = assume.zip(cannot_unwind).zip(in_cleanup).map(
            |((assume, cannot_unwind), in_cleanup)| AssertFailureCalls {
                assume,
                cannot_unwind,
                in_cleanup,
            },
        );
        CowBox::Owned(Box::new(Self { calls }))
    }
}

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.reconstruct_asserts
    }

    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        let Some(calls) = &self.calls else { return };
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

                use UnwindTerminateReason::*;
                let call = match abort {
                    AbortKind::Panic => call.clone().expect("panic always has a call"),
                    AbortKind::UndefinedBehavior => calls.assume.clone(),
                    AbortKind::UnwindTerminate(Abi) => calls.cannot_unwind.clone(),
                    AbortKind::UnwindTerminate(InCleanup) => calls.in_cleanup.clone(),
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
