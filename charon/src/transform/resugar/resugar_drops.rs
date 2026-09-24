//! Reconstruct conditional drops by detecting some drop-flag usage patterns that rustc emits. This
//! is not complete, but is correct: we check that the drop flags faithfully track the drop status
//! of places.
use std::collections::HashMap;
use std::mem;
use std::ops::ControlFlow;

use derive_generic_visitor::Visitor;
use itertools::Itertools;
use macros::{EnumAsGetters, EnumIsA};
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::{Dfs, Walker};

use crate::options::TranslateOptions;
use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;

impl Rvalue {
    fn as_const_bool(&self) -> Option<bool> {
        if let Rvalue::Use(Operand::Const(value), _) = self
            && let ConstantExprKind::Bool(value) = value.kind()
        {
            Some(*value)
        } else {
            None
        }
    }
}

#[derive(Debug, EnumIsA)]
enum FlagStatus {
    /// This boolean may or may not be a drop flag.
    Unknown {
        /// Locations where this local is assigned to.
        assigned: Vec<StmtLoc>,
    },
    /// This boolean so far meets all the criteria for being a drop flag for the given place.
    Valid {
        place: Place,
        /// Locations where this local is assigned to.
        assigned: Vec<StmtLoc>,
    },
    /// This boolean was used in a way that doesn't match drop flags,
    /// or at least that we don't know how to reconstruct.
    Discarded,
}

impl Default for FlagStatus {
    fn default() -> Self {
        Self::Unknown {
            assigned: Vec::new(),
        }
    }
}

struct ConditionalDrop {
    flag: LocalId,
    /// The block that switched on the drop flag.
    switch_block: BlockId,
    /// The block that contains the unconditional drop.
    drop_block: BlockId,
}

#[derive(Visitor)]
struct GatherCandidates<'a> {
    body: &'a ExprBody,
    /// The number of predecessors of each block.
    predecessor_counts: IndexVec<BlockId, usize>,
    /// For each boolean local, compute whether it is used like a drop flag, and if so for which
    /// place.
    flag_statuses: IndexVec<LocalId, FlagStatus>,
    /// Accumulate candidates for conditional drops.
    conditional_drops: Vec<ConditionalDrop>,
    /// The block currently being visited.
    current_block: Option<BlockId>,
    /// The statement currently being visited.
    current_statement: Option<StmtLoc>,
}

impl VisitBody for GatherCandidates<'_> {
    fn enter_local_id(&mut self, local: &LocalId) {
        // If we get here, the local is being used in a way that drop flags aren't used.
        self.flag_statuses[*local] = FlagStatus::Discarded;
    }

    fn visit_ullbc_block(&mut self, block: &BlockData) -> ControlFlow<Self::Break> {
        let block_id = self.current_block.unwrap();
        for (stmt_id, statement) in block.statements.iter().enumerate() {
            self.current_statement = Some(StmtLoc::new(block_id, stmt_id));
            self.visit(statement)?;
        }
        self.current_statement = None;
        self.visit(&block.terminator)
    }

    fn visit_ullbc_statement(&mut self, statement: &Statement) -> ControlFlow<Self::Break> {
        match &statement.kind {
            // A drop flag may be assigned a constant value.
            StatementKind::Assign(place, rval)
                if let Some(local) = place.as_local()
                    && rval.as_const_bool().is_some() =>
            {
                match &mut self.flag_statuses[local] {
                    FlagStatus::Unknown { assigned } | FlagStatus::Valid { assigned, .. } => {
                        assigned.push(self.current_statement.unwrap())
                    }
                    FlagStatus::Discarded => {}
                }
                ControlFlow::Continue(())
            }
            _ => self.visit_inner(statement),
        }
    }

    fn visit_ullbc_terminator(&mut self, terminator: &Terminator) -> ControlFlow<Self::Break> {
        // Find branches over booleans with drops in one of the branches.
        if let TerminatorKind::Switch { data, branches } = &terminator.kind
            && let SwitchScrutinee::Value(Operand::Copy(flag_place) | Operand::Move(flag_place)) =
                &data.scrutinee
            && let Some(flag) = flag_place.as_local()
            && !self.flag_statuses[flag].is_discarded()
            && let Some((true_branch, false_branch)) = data.as_if()
        {
            let true_target = branches[true_branch];
            let false_target = branches[false_branch];
            let drop_block = &self.body.body[true_target];

            // Detect a simple pattern: `if drop_flag { unconditional_drop } else {}`.
            if true_target != false_target
                && self.predecessor_counts[true_target] == 1
                && let TerminatorKind::Drop {
                    kind: DropKind::Precise,
                    place,
                    target,
                    ..
                } = &drop_block.terminator.kind
                && drop_block.statements.is_empty()
                && *target == false_target
            {
                let status = &mut self.flag_statuses[flag];
                match status {
                    FlagStatus::Unknown { assigned } => {
                        *status = FlagStatus::Valid {
                            place: place.clone(),
                            assigned: mem::take(assigned),
                        }
                    }
                    FlagStatus::Valid {
                        place: previous, ..
                    } if previous != place => *status = FlagStatus::Discarded,
                    FlagStatus::Valid { .. } | FlagStatus::Discarded => {}
                }
                if status.is_valid() {
                    self.conditional_drops.push(ConditionalDrop {
                        flag,
                        switch_block: self.current_block.unwrap(),
                        drop_block: true_target,
                    });
                }
                ControlFlow::Continue(())
            } else {
                self.visit_inner(terminator)
            }
        } else {
            self.visit_inner(terminator)
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct AnalysisState {
    flag_value: bool,
    place_is_initialized: bool,
}

impl AnalysisState {
    /// All possible states.
    fn all() -> impl Iterator<Item = Self> {
        [false, true]
            .into_iter()
            .cartesian_product([false, true])
            .map(|(flag_value, place_is_initialized)| Self {
                flag_value,
                place_is_initialized,
            })
    }

    fn is_consistent(self) -> bool {
        self.flag_value == self.place_is_initialized
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum AnalysisNode {
    Root,
    State {
        block: BlockId,
        flag: LocalId,
        state: AnalysisState,
    },
    Invalid(LocalId),
}

#[derive(Debug, Default, Copy, Clone, EnumAsGetters)]
enum Update<T> {
    #[default]
    Unchanged,
    Set(T),
}

impl<T: Copy> Update<T> {
    fn apply(self, value: T) -> T {
        match self {
            Self::Unchanged => value,
            Self::Set(value) => value,
        }
    }
}

#[derive(Debug, Default, Copy, Clone)]
struct FlagUpdate {
    flag_value: Update<bool>,
    place_is_initialized: Update<bool>,
}

impl FlagUpdate {
    fn apply(self, state: AnalysisState) -> AnalysisState {
        AnalysisState {
            flag_value: self.flag_value.apply(state.flag_value),
            place_is_initialized: self.place_is_initialized.apply(state.place_is_initialized),
        }
    }
}

/// For each CFG node and each flag, we record the possible states of both the flag value and
/// initialization status of the corresponding place. We then add an edge to the graph when one can
/// transition between two such states. We then check if an invalid node is reachable; if not, then
/// the boolean flag faithfully represents the initialization status of the place!
struct CheckFlagCorrectness<'a> {
    /// List of candidate drop flags, with the place they correspond to.
    flags: Vec<(LocalId, &'a Place)>,
    graph: DiGraphMap<AnalysisNode, ()>,
    /// For each block, the updates to candidate flags affected by the block.
    updates: IndexVec<BlockId, HashMap<LocalId, FlagUpdate>>,
}

#[derive(Visitor)]
struct ComputeUpdates<'a, 'body> {
    analysis: &'a mut CheckFlagCorrectness<'body>,
    block_id: BlockId,
}

impl VisitBody for ComputeUpdates<'_, '_> {
    fn enter_operand(&mut self, operand: &Operand) {
        if let Operand::Move(moved) = operand {
            let updates = &mut self.analysis.updates[self.block_id];
            for &(flag, place) in &self.analysis.flags {
                if place.is_subplace(moved) {
                    updates.entry(flag).or_default().place_is_initialized = Update::Set(false);
                }
            }
        }
    }

    fn exit_ullbc_statement(&mut self, statement: &Statement) {
        match &statement.kind {
            StatementKind::Assign(assigned, rval) => {
                let updates = &mut self.analysis.updates[self.block_id];
                for &(flag, place) in &self.analysis.flags {
                    if assigned.as_local() == Some(flag) {
                        // Unwrap is ok because we made sure this is only assigned constants.
                        let value = rval.as_const_bool().unwrap();
                        updates.entry(flag).or_default().flag_value = Update::Set(value);
                    }
                    if place.is_subplace(assigned) {
                        updates.entry(flag).or_default().place_is_initialized = Update::Set(true);
                    }
                }
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                let updates = &mut self.analysis.updates[self.block_id];
                for &(flag, place) in &self.analysis.flags {
                    if place.local_id() == Some(*local) {
                        updates.entry(flag).or_default().place_is_initialized = Update::Set(false);
                    }
                }
            }
            _ => {}
        }
    }
}

impl<'a> CheckFlagCorrectness<'a> {
    /// Check if these drop flags correctly track the corresponding place. Returns the ones that
    /// don't.
    fn compute_invalid_flags(body: &ExprBody, flags: Vec<(LocalId, &'a Place)>) -> Vec<LocalId> {
        let updates = body.body.map_ref(|_| HashMap::new());
        let mut graph = DiGraphMap::new();
        graph.add_node(AnalysisNode::Root);
        let mut analysis = Self {
            flags,
            updates,
            graph,
        };
        analysis.compute_updates(body);
        analysis.build_graph(body);
        Dfs::new(&analysis.graph, AnalysisNode::Root)
            .iter(&analysis.graph)
            .filter_map(|node| match node {
                AnalysisNode::Invalid(flag) => Some(flag),
                AnalysisNode::Root | AnalysisNode::State { .. } => None,
            })
            .collect()
    }

    /// Summarize how each block changes each candidate flag and its associated place.
    fn compute_updates(&mut self, body: &ExprBody) {
        for (block_id, block) in body.body.iter_enumerated() {
            ComputeUpdates {
                analysis: self,
                block_id,
            }
            .visit(block);
        }
    }

    /// Build a graph that has an edge for every valid state transition.
    fn build_graph(&mut self, body: &ExprBody) {
        for &(flag, place) in &self.flags {
            // Drop flags get initialized in the first block.
            let node = if let Some(update) = self.updates[START_BLOCK_ID].get(&flag)
                && let Some(flag_value) = update.flag_value.as_set().copied()
            {
                let initially_initialized = place.local_id().is_none_or(|local| {
                    local.index() > 0 && local.index() <= body.locals.arg_count
                });
                AnalysisNode::State {
                    block: START_BLOCK_ID,
                    flag,
                    state: AnalysisState {
                        flag_value,
                        place_is_initialized: initially_initialized,
                    },
                }
            } else {
                AnalysisNode::Invalid(flag)
            };
            self.graph.add_edge(AnalysisNode::Root, node, ());
        }

        for (block_id, block) in body.body.iter_enumerated() {
            for &(flag, place) in &self.flags {
                let update = self.updates[block_id]
                    .get(&flag)
                    .copied()
                    .unwrap_or_default();
                for initial_state in AnalysisState::all() {
                    let source = AnalysisNode::State {
                        block: block_id,
                        flag,
                        state: initial_state,
                    };
                    let state = update.apply(initial_state);
                    if let Some(successors) = Self::block_successors(block, flag, place, state) {
                        for (target, state) in successors {
                            self.graph.add_edge(
                                source,
                                AnalysisNode::State {
                                    block: target,
                                    flag,
                                    state,
                                },
                                (),
                            );
                        }
                    } else {
                        self.graph.add_edge(source, AnalysisNode::Invalid(flag), ());
                    }
                }
            }
        }
    }

    /// Compute the reachable states from this one at the end of a block. `None` means that the
    /// state is inconsistent and the drop flag is invalid.
    fn block_successors(
        block: &BlockData,
        flag: LocalId,
        place: &Place,
        mut state: AnalysisState,
    ) -> Option<Vec<(BlockId, AnalysisState)>> {
        if let TerminatorKind::Switch { data, branches } = &block.terminator.kind
            && let SwitchScrutinee::Value(Operand::Copy(flag_place) | Operand::Move(flag_place)) =
                &data.scrutinee
            && flag_place.as_local() == Some(flag)
        {
            // The only place that state consistency matters is when switching on the boolean flag.
            if !state.is_consistent() {
                return None;
            }
            let (true_branch, false_branch) = data.as_if()?;
            let branch = if state.flag_value {
                true_branch
            } else {
                false_branch
            };
            Some(vec![(branches[branch], state)])
        } else {
            Some(match &block.terminator.kind {
                TerminatorKind::Call {
                    call,
                    target,
                    on_unwind,
                } => {
                    let mut after_return = state;
                    if place.is_subplace(&call.dest) {
                        after_return.place_is_initialized = true;
                    }
                    vec![(*target, after_return), (*on_unwind, state)]
                }
                TerminatorKind::Drop {
                    place: dropped,
                    target,
                    on_unwind,
                    ..
                } => {
                    if place.is_subplace(dropped) {
                        state.place_is_initialized = false;
                    }
                    vec![(*target, state), (*on_unwind, state)]
                }
                _ => block
                    .terminator
                    .targets()
                    .into_iter()
                    .map(|target| (target, state))
                    .collect(),
            })
        }
    }
}

pub struct Transform;
impl UllbcPass for Transform {
    fn should_run(&self, options: &TranslateOptions) -> bool {
        options.resugar_drops
    }

    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ExprBody) {
        if !body.body.iter().any(|block| {
            matches!(
                block.terminator.kind,
                TerminatorKind::Drop {
                    kind: DropKind::Precise,
                    ..
                }
            )
        }) {
            return;
        }

        let mut predecessor_counts = body.body.map_ref(|_| 0usize);
        for block in &body.body {
            for target in block.terminator.targets() {
                predecessor_counts[target] += 1;
            }
        }

        // Start with anonymous boolean locals.
        let mut flag_statuses: IndexVec<LocalId, FlagStatus> =
            body.locals.locals.map_ref(|local| {
                if local.name.is_none()
                    && !body.locals.is_return_or_arg(local.index)
                    && local.ty.is_bool()
                {
                    FlagStatus::default()
                } else {
                    FlagStatus::Discarded
                }
            });

        // Go through the body to find locals that could be drop flags and locations that could be
        // conditional drops.
        let conditional_drops = {
            let mut visitor = GatherCandidates {
                body,
                predecessor_counts,
                flag_statuses,
                conditional_drops: Vec::new(),
                current_block: None,
                current_statement: None,
            };
            for (block_id, block) in body.body.iter_enumerated() {
                visitor.current_block = Some(block_id);
                visitor.visit(block);
            }
            flag_statuses = visitor.flag_statuses;
            visitor.conditional_drops
        };

        // Check that each flag correctly reflects the initialization status of its corresponding
        // place.
        let invalid_flags = {
            let flags = flag_statuses
                .iter_enumerated()
                .filter_map(|(flag, status)| match status {
                    FlagStatus::Valid { place, .. } => Some((flag, place)),
                    FlagStatus::Unknown { .. } | FlagStatus::Discarded => None,
                })
                .collect();
            CheckFlagCorrectness::compute_invalid_flags(body, flags)
        };
        for flag in invalid_flags {
            flag_statuses[flag] = FlagStatus::Discarded;
        }

        for drop in conditional_drops {
            if let FlagStatus::Valid { assigned, .. } = &flag_statuses[drop.flag] {
                let mut terminator = body.body[drop.drop_block].terminator.kind.take();
                let TerminatorKind::Drop { kind, .. } = &mut terminator else {
                    unreachable!()
                };
                *kind = DropKind::Conditional;
                body.body[drop.switch_block].terminator.kind = terminator;
                // Remove the assignments; the unused-locals pass will then remove them entirely.
                for loc in assigned {
                    body[*loc].kind = StatementKind::Nop;
                }
            }
        }
    }
}
