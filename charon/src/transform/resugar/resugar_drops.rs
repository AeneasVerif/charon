//! Reconstruct conditional drops using the drop flags identified by `detect_drop_flags`.
use crate::options::TranslateOptions;
use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;

struct ConditionalDrop {
    /// The block that switched on the drop flag.
    switch_block: BlockId,
    /// The block that contains the unconditional drop.
    drop_block: BlockId,
}

#[derive(Default)]
struct FlagUses {
    assignments: Vec<StmtLoc>,
    if_count: usize,
    resugared_if_count: usize,
}

pub struct Transform;
impl UllbcPass for Transform {
    fn should_run(&self, options: &TranslateOptions) -> bool {
        options.resugar_drops
    }

    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ExprBody) {
        let mut predecessor_counts = body.body.map_ref(|_| 0usize);
        for block in &body.body {
            for target in block.terminator.targets() {
                predecessor_counts[target] += 1;
            }
        }

        let mut flag_uses = body.locals.locals.map_ref(|_| FlagUses::default());
        let mut conditional_drops = Vec::new();

        for (block_id, block) in body.body.iter_enumerated() {
            for (statement_id, statement) in block.statements.iter().enumerate() {
                if let StatementKind::Assign(place, _) = &statement.kind
                    && let Some(flag) = place.as_local()
                    && body.locals.locals[flag].drop_flag_for.is_some()
                {
                    flag_uses[flag]
                        .assignments
                        .push(StmtLoc::new(block_id, statement_id));
                }
            }

            if let TerminatorKind::Switch { data, branches } = &block.terminator.kind
                && let SwitchScrutinee::Value(Operand::Copy(flag_place) | Operand::Move(flag_place)) =
                    &data.scrutinee
                && let Some(flag) = flag_place.as_local()
                && let Some(flagged_place) = &body.locals.locals[flag].drop_flag_for
                && let Some((true_branch, false_branch)) = data.as_if()
            {
                flag_uses[flag].if_count += 1;
                let true_target = branches[true_branch];
                let false_target = branches[false_branch];
                let drop_block = &body.body[true_target];

                // Detect a simple pattern: `if drop_flag { unconditional_drop } else {}`.
                if true_target != false_target
                    && predecessor_counts[true_target] == 1
                    && let TerminatorKind::Drop {
                        kind: DropKind::Precise,
                        place,
                        target,
                        ..
                    } = &drop_block.terminator.kind
                    && place == flagged_place
                    && drop_block.statements.is_empty()
                    && *target == false_target
                {
                    flag_uses[flag].resugared_if_count += 1;
                    conditional_drops.push(ConditionalDrop {
                        switch_block: block_id,
                        drop_block: true_target,
                    });
                }
            }
        }

        for drop in conditional_drops {
            let mut terminator = body.body[drop.drop_block].terminator.kind.take();
            let TerminatorKind::Drop { kind, .. } = &mut terminator else {
                unreachable!()
            };
            *kind = DropKind::Conditional;
            body.body[drop.switch_block].terminator.kind = terminator;
        }

        // If every use of a flag has been resugared, remove its assignments. The unused-locals
        // pass will then remove the local entirely.
        for uses in flag_uses {
            if uses.if_count == uses.resugared_if_count {
                for loc in uses.assignments {
                    body[loc].kind = StatementKind::Nop;
                }
            }
        }
    }
}
