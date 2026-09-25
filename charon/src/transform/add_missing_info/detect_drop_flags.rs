//! Detect the boolean locals that rustc uses to track whether a place needs to be dropped.
//!
//! This may miss some drop flags but the ones it detects are guaranteed to be correct, as we do
//! a control-flow analysis to be sure.
use std::collections::HashMap;
use std::ops::ControlFlow;

use derive_generic_visitor::Visitor;
use itertools::Itertools;
use macros::EnumAsGetters;
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

#[derive(Debug, Default)]
enum FlagStatus {
    /// We have tot encountered a switch on this boolean yet.
    #[default]
    Unknown,
    /// This boolean has only been assigned constants and switched on, hence is a candidate drop
    /// flag. The places are these that were unconditionally dropped in every true branch of
    /// a switch on this flag.
    Candidate { dropped_places: Vec<Place> },
    /// This boolean was used in a way that drop flags aren't used.
    Discarded,
}

#[derive(Visitor)]
struct GatherCandidates<'a> {
    body: &'a ExprBody,
    flag_statuses: IndexVec<LocalId, FlagStatus>,
}

impl GatherCandidates<'_> {
    /// Follow the true branch until it reaches the false target, and accumulate any place that
    /// gets unconditionally dropped along the way. We ignore unwind paths and other switches.
    fn dropped_places_in_true_branch(
        &self,
        true_target: BlockId,
        false_target: BlockId,
    ) -> Vec<Place> {
        let mut dropped_places = Vec::new();
        let mut visited = self.body.body.map_ref(|_| false);
        let mut pending = vec![true_target];

        while let Some(block_id) = pending.pop() {
            if block_id == false_target || std::mem::replace(&mut visited[block_id], true) {
                continue;
            }

            let terminator = &self.body.body[block_id].terminator;
            if let TerminatorKind::Drop {
                kind: DropKind::Precise,
                place,
                ..
            } = &terminator.kind
                && !dropped_places.contains(place)
            {
                dropped_places.push(place.clone());
            }
            pending.extend(terminator.targets_ignoring_unwind());
        }

        dropped_places
    }
}

impl VisitBody for GatherCandidates<'_> {
    fn enter_local_id(&mut self, local: &LocalId) {
        // If we get here, the local is being used in a way that drop flags aren't used.
        self.flag_statuses[*local] = FlagStatus::Discarded;
    }

    fn visit_ullbc_statement(&mut self, statement: &Statement) -> ControlFlow<Self::Break> {
        match &statement.kind {
            // A drop flag may only be assigned a constant value.
            StatementKind::Assign(place, rval)
                if let Some(_local) = place.as_local()
                    && rval.as_const_bool().is_some() =>
            {
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
            && !matches!(&self.flag_statuses[flag], FlagStatus::Discarded)
            && let Some((true_branch, false_branch)) = data.as_if()
        {
            let true_target = branches[true_branch];
            let false_target = branches[false_branch];
            let dropped_places = self.dropped_places_in_true_branch(true_target, false_target);
            let status = &mut self.flag_statuses[flag];
            match status {
                FlagStatus::Unknown => {
                    *status = FlagStatus::Candidate { dropped_places };
                }
                FlagStatus::Candidate {
                    dropped_places: candidates,
                } => {
                    candidates.retain(|place| dropped_places.contains(place));
                    if dropped_places.is_empty() {
                        *status = FlagStatus::Discarded;
                    }
                }
                FlagStatus::Discarded => unreachable!(),
            }
            ControlFlow::Continue(())
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
struct CheckFlagCorrectness<'a, 'b> {
    /// List of candidate drop flags, with the place they correspond to.
    flags: &'b mut SeqHashMap<LocalId, &'a Place>,
    graph: DiGraphMap<AnalysisNode, ()>,
    /// For each block, the updates to candidate flags affected by the block.
    updates: IndexVec<BlockId, HashMap<LocalId, FlagUpdate>>,
}

#[derive(Visitor)]
struct ComputeUpdates<'a, 'b, 'c> {
    analysis: &'a mut CheckFlagCorrectness<'b, 'c>,
    block_id: BlockId,
}

impl VisitBody for ComputeUpdates<'_, '_, '_> {
    fn enter_operand(&mut self, operand: &Operand) {
        if let Operand::Move(moved) = operand {
            let updates = &mut self.analysis.updates[self.block_id];
            for (&flag, place) in self.analysis.flags.iter() {
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
                for (&flag, place) in self.analysis.flags.iter() {
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
                for (&flag, place) in self.analysis.flags.iter() {
                    if place.local_id() == Some(*local) {
                        updates.entry(flag).or_default().place_is_initialized = Update::Set(false);
                    }
                }
            }
            _ => {}
        }
    }
}

impl<'a, 'b> CheckFlagCorrectness<'a, 'b> {
    /// Check if these drop flags correctly track the corresponding place. Removes the ones that
    /// don't.
    fn filter_invalid_flags(body: &ExprBody, flags: &'b mut SeqHashMap<LocalId, &'a Place>) {
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
        for flag in Dfs::new(&analysis.graph, AnalysisNode::Root)
            .iter(&analysis.graph)
            .filter_map(|node| match node {
                AnalysisNode::Invalid(flag) => Some(flag),
                AnalysisNode::Root | AnalysisNode::State { .. } => None,
            })
        {
            analysis.flags.swap_remove(&flag);
        }
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
        for (&flag, place) in self.flags.iter() {
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
            for (&flag, place) in self.flags.iter() {
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
        options.detect_drop_flags || options.resugar_drops
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

        // Start with anonymous boolean locals.
        let flag_statuses: IndexVec<LocalId, FlagStatus> = body.locals.locals.map_ref(|local| {
            if local.name.is_none()
                && !body.locals.is_return_or_arg(local.index)
                && local.ty.is_bool()
            {
                FlagStatus::default()
            } else {
                FlagStatus::Discarded
            }
        });

        // Identify booleans that are used like drop flags, and find out what place they track.
        let flag_statuses = {
            let mut visitor = GatherCandidates {
                body,
                flag_statuses,
            };
            for block in &body.body {
                visitor.visit(block);
            }
            visitor.flag_statuses
        };

        // Keep flags for which we know the tracked place, then check that they do in fact track
        // the initializedness of that place.
        let mut flag_candidates: SeqHashMap<LocalId, &Place> = flag_statuses
            .iter_enumerated()
            .filter_map(|(flag, status)| match status {
                FlagStatus::Candidate { dropped_places } => {
                    let place = dropped_places.iter().exactly_one().ok()?;
                    Some((flag, place))
                }
                FlagStatus::Unknown | FlagStatus::Discarded => None,
            })
            .collect();
        CheckFlagCorrectness::filter_invalid_flags(body, &mut flag_candidates);
        for (flag, place) in flag_candidates {
            body.locals.locals[flag].drop_flag_for = Some(place.clone());
        }
    }
}
