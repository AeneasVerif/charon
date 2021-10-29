//! IM to CFIM (Control-Flow Internal MIR)

use crate::cfim_ast as tgt;
use crate::im_ast as src;
use crate::translate_functions_to_im::FunTransContext;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use im;
use im::Vector;
use petgraph::algo::dominators::simple_fast;
use petgraph::algo::floyd_warshall::floyd_warshall;
use petgraph::algo::simple_paths::all_simple_paths;
use petgraph::algo::toposort;
use petgraph::graphmap::DiGraphMap;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

pub type Decls = tgt::FunDecls;

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId::Id, ()>;

fn get_block_targets(decl: &src::FunDecl, block_id: src::BlockId::Id) -> Vec<src::BlockId::Id> {
    let block = decl.body.get(block_id).unwrap();

    match &block.terminator {
        src::Terminator::Goto { target }
        | src::Terminator::Drop { place: _, target }
        | src::Terminator::Call {
            func: _,
            region_params: _,
            type_params: _,
            args: _,
            dest: _,
            target,
        }
        | src::Terminator::Assert {
            cond: _,
            expected: _,
            target,
        } => {
            vec![*target]
        }
        src::Terminator::Switch { discr: _, targets } => targets.get_targets(),
        src::Terminator::Panic | src::Terminator::Unreachable | src::Terminator::Return => {
            vec![]
        }
    }
}

/// This structure contains various information about a function's CFG.
struct CfgPartialInfo {
    /// The CFG
    pub cfg: Cfg,
    /// The CFG where all the backward edges have been removed
    pub cfg_no_be: Cfg,
    /// We consider the destination of the backward edges to be loop entries and
    /// store them here.
    pub loop_entries: HashSet<src::BlockId::Id>,
    /// The backward edges
    pub backward_edges: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
    /// The blocks whose terminators are a switch are stored here.
    pub switch_blocks: HashSet<src::BlockId::Id>,
}

/// Similar to `CfgPartialInfo`, but with more information
struct CfgInfo {
    pub cfg: Cfg,
    pub cfg_no_be: Cfg,
    pub loop_entries: HashSet<src::BlockId::Id>,
    pub backward_edges: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
    pub switch_blocks: HashSet<src::BlockId::Id>,
    /// The reachability graph:
    /// src can reach dest <==> (src, dest) in reachability
    pub reachability: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
    /// Dominators (on the CFG *without* back-edges):
    /// n dominated by n' <==> (n, n') in dominated
    pub dominated_no_be: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
}

/// Build the CFGs (the "regular" CFG and the CFG without backward edges) and
/// compute some information like the loop entries and the switch blocks.
fn build_cfg_partial_info(decl: &src::FunDecl) -> CfgPartialInfo {
    let mut cfg = CfgPartialInfo {
        cfg: Cfg::new(),
        cfg_no_be: Cfg::new(),
        loop_entries: HashSet::new(),
        backward_edges: HashSet::new(),
        switch_blocks: HashSet::new(),
    };

    // Add the nodes
    for block_id in decl.body.iter_indices() {
        cfg.cfg.add_node(block_id);
        cfg.cfg_no_be.add_node(block_id);
    }

    // Add the edges
    let ancestors = im::HashSet::new();
    let mut explored = im::HashSet::new();
    build_cfg_partial_info_edges(
        &mut cfg,
        &ancestors,
        &mut explored,
        decl,
        src::BlockId::ZERO,
    );

    cfg
}

fn block_is_switch(decl: &src::FunDecl, block_id: src::BlockId::Id) -> bool {
    let block = decl.body.get(block_id).unwrap();
    block.terminator.is_switch()
}

fn build_cfg_partial_info_edges(
    cfg: &mut CfgPartialInfo,
    ancestors: &im::HashSet<src::BlockId::Id>,
    explored: &mut im::HashSet<src::BlockId::Id>,
    decl: &src::FunDecl,
    block_id: src::BlockId::Id,
) {
    // Check if we already explored the current node
    if explored.contains(&block_id) {
        return;
    }
    explored.insert(block_id);

    // Insert the current block in the set of ancestors blocks
    let mut ancestors = ancestors.clone();
    ancestors.insert(block_id);

    // Check if it is a switch
    if block_is_switch(decl, block_id) {
        cfg.switch_blocks.insert(block_id);
    }

    // Retrieve the block targets
    let targets = get_block_targets(decl, block_id);

    // Add edges for all the targets and explore them, if they are not predecessors
    for tgt in &targets {
        // Insert the edge in the "regular" CFG
        cfg.cfg.add_edge(block_id, *tgt, ());

        // We need to check if it is a backward edge before inserting it in the
        // CFG without backward edges and exploring it
        if ancestors.contains(tgt) {
            // This is a backward edge
            cfg.loop_entries.insert(*tgt);
            cfg.backward_edges.insert((block_id, *tgt));
        } else {
            // Not a backward edge: insert the edge and explore
            cfg.cfg_no_be.add_edge(block_id, *tgt, ());
            build_cfg_partial_info_edges(cfg, &ancestors, explored, decl, *tgt);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OrdBlockId {
    id: src::BlockId::Id,
    /// The rank in the topological order
    rank: usize,
}

impl Ord for OrdBlockId {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rank.cmp(&other.rank)
    }
}

impl PartialOrd for OrdBlockId {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Compute the reachability matrix for a graph.
///
/// We represent the reachability matrix as a set such R that:
/// there exists a path from src to dest <==> (src, dest) in R
fn compute_reachability(cfg: &CfgPartialInfo) -> HashSet<(src::BlockId::Id, src::BlockId::Id)> {
    // We simply use Floyd-Warshall.
    // We just need to be a little careful: we have to make sure the value we
    // use for infinity is never reached. That is to say, that there are stricly
    // less edges in the graph than usize::MAX.
    // Note that for now, the assertion will actually always statically succeed,
    // because `edge_count` returns a usize... It still is good to keep it there.
    assert!(cfg.cfg.edge_count() < std::usize::MAX);

    let fw_matrix: HashMap<(src::BlockId::Id, src::BlockId::Id), usize> =
        floyd_warshall(&cfg.cfg, &|_| 1).unwrap();

    // Convert the fw_matrix
    let reachability: HashSet<(src::BlockId::Id, src::BlockId::Id)> =
        HashSet::from_iter(fw_matrix.into_iter().filter_map(|((src, dst), dest)| {
            if dest == std::usize::MAX {
                None
            } else {
                Some((src, dst))
            }
        }));

    reachability
}

/// Compute the domination matrix, on the CFG *without* back edges.
///
/// We represent the domination matrix as a set R such that:
/// n dominated by n' <==> (n, n') in R
fn compute_dominated_no_be(cfg: &CfgPartialInfo) -> HashSet<(src::BlockId::Id, src::BlockId::Id)> {
    // We simply use tarjan
    let dominators = simple_fast(&cfg.cfg_no_be, src::BlockId::ZERO);

    let mut matrix = HashSet::new();

    for n in cfg.cfg_no_be.nodes() {
        match dominators.dominators(n) {
            None => (),
            Some(dominators) => {
                for d in dominators {
                    matrix.insert((n, d));
                }
            }
        }
    }

    matrix
}

fn compute_cfg_info_from_partial(cfg: CfgPartialInfo) -> CfgInfo {
    let reachability = compute_reachability(&cfg);
    let dominated_no_be = compute_dominated_no_be(&cfg);

    let CfgPartialInfo {
        cfg,
        cfg_no_be,
        loop_entries,
        backward_edges,
        switch_blocks,
    } = cfg;

    CfgInfo {
        cfg,
        cfg_no_be,
        loop_entries,
        backward_edges,
        switch_blocks,
        reachability,
        dominated_no_be,
    }
}

#[derive(Debug, Clone)]
struct LoopExitCandidateInfo {
    /// The occurrences going to this exit.
    /// For every occurrence, we register the distance between the loop entry
    /// and the node from which the edge going to the exit starts.
    /// If later we have to choose between candidates with the same number
    /// of occurrences, we choose the one with the smallest distances.
    pub occurrences: Vec<usize>,
}

/// Check if a loop entry is reachable from a node, in a graph where we remove
/// the backward edges going directly to the loop entry.
///
/// If the loop entry is not reachable, it means that:
/// - the loop entry is not reachable at all
/// - or it is only reachable through an outer loop
///
/// The starting node should be a (transitive) child of the loop entry.
/// We use this to find candidates for loop exits.
///
/// Rk.: this is not efficient at all.
fn loop_entry_is_reachable_from_inner(
    cfg: &CfgInfo,
    loop_entry: src::BlockId::Id,
    block_id: src::BlockId::Id,
) -> bool {
    // Shortcut: the loop entry is not reachable at all
    if !cfg.reachability.contains(&(block_id, loop_entry)) {
        return false;
    }

    // It is reachable in the complete graph. Check if it is reachable through
    // a backward edge which doesn't go directly to the loop entry (i.e.: through
    // a backward edge which requires going to an outer loop).
    // We check this in a very simple way: we just explore all the simple paths,
    // and eliminate those which contain a backward edge whose destination is
    // the loop entry. Once again: we're not looking for efficiency here.
    'outer: for path in
        all_simple_paths::<Vec<src::BlockId::Id>, &Cfg>(&cfg.cfg, block_id, loop_entry, 0, None)
    {
        let mut prev_node = block_id;
        for n in path {
            if cfg.backward_edges.contains(&(prev_node, n)) {
                if n == loop_entry {
                    return true;
                } else {
                    continue 'outer;
                }
            } else {
                prev_node = n;
            }
        }

        // If we get there, it means that the path contains no backward edge
        // which is impossible
        unreachable!();
    }

    // No path contains a backward edge which goes directly to the loop entry
    return false;
}

fn filter_loop_parents(
    cfg: &CfgInfo,
    parent_loops: &Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) -> Option<Vector<(src::BlockId::Id, usize)>> {
    let mut eliminate: usize = 0;
    let mut distance: usize = 0;
    for (loop_id, ldist) in parent_loops.iter().rev() {
        if !loop_entry_is_reachable_from_inner(cfg, *loop_id, block_id) {
            eliminate += 1;
            distance += *ldist;
        } else {
            break;
        }
    }

    if eliminate > 0 {
        // Truncate the vector of parents
        let mut out = Vector::new();
        for i in 0..(parent_loops.len() - eliminate) {
            out.push_back(parent_loops[i]);
        }

        // Update the distance to the last loop
        if !out.is_empty() {
            out.get_mut(out.len() - 1).unwrap().1 += distance;
        }

        Some(out)
    } else {
        None
    }
}

fn register_loop_exit_candidate(
    loop_exits: &mut HashMap<src::BlockId::Id, HashMap<src::BlockId::Id, LoopExitCandidateInfo>>,
    parent_loops: &Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) {
    let parent = parent_loops.get(parent_loops.len() - 1).unwrap();
    let loop_id = parent.0;
    let distance = parent.1;

    let candidates = loop_exits.get_mut(&loop_id).unwrap();
    match candidates.get_mut(&block_id) {
        None => {
            candidates.insert(
                block_id,
                LoopExitCandidateInfo {
                    occurrences: vec![distance],
                },
            );
        }
        Some(c) => {
            c.occurrences.push(distance);
        }
    }
}

fn compute_loop_exit_candidates(
    cfg: &CfgInfo,
    explored: &mut HashSet<src::BlockId::Id>,
    ordered_loops: &mut Vec<src::BlockId::Id>,
    loop_exits: &mut HashMap<src::BlockId::Id, HashMap<src::BlockId::Id, LoopExitCandidateInfo>>,
    // List of parent loops, with the distance to the entry of the loop (the distance
    // is the distance between the current node and the loop entry for the last parent,
    // and the distance between the parents for the others).
    mut parent_loops: Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) {
    if explored.contains(&block_id) {
        return;
    }
    explored.insert(block_id);

    // Check if we enter a loop - add the corresponding node if necessary
    if cfg.loop_entries.contains(&block_id) {
        parent_loops.push_back((block_id, 1));
        ordered_loops.push(block_id);
    } else {
        // Increase the distance with the parent loop
        if !parent_loops.is_empty() {
            parent_loops.get_mut(parent_loops.len() - 1).unwrap().1 += 1;
        }
    };

    // Retrieve the children - note that we ignore the back edges
    let children = cfg.cfg_no_be.neighbors(block_id);
    for child in children {
        // If the parent loop entry is not reachable from the child without going
        // through a backward edge which goes directly to the loop entry, consider
        // this node a potential exit.
        match filter_loop_parents(cfg, &parent_loops, child) {
            None => {
                compute_loop_exit_candidates(
                    cfg,
                    explored,
                    ordered_loops,
                    loop_exits,
                    parent_loops.clone(),
                    child,
                );
            }
            Some(fparent_loops) => {
                // We filtered some parent loops: it means this child is a loop
                // exit candidate. Register it.
                register_loop_exit_candidate(loop_exits, &parent_loops, child);

                // Explore, with the filtered parents
                compute_loop_exit_candidates(
                    cfg,
                    explored,
                    ordered_loops,
                    loop_exits,
                    fparent_loops,
                    child,
                );
            }
        }
    }
}

/// TODO: explanations
fn compute_loop_exits(cfg: &CfgInfo) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
    let mut explored = HashSet::new();
    let mut ordered_loops = Vec::new();
    let mut loop_exits = HashMap::new();

    // Initialize the loop exits candidates
    for loop_id in &cfg.loop_entries {
        loop_exits.insert(*loop_id, HashMap::new());
    }

    // Compute the candidates
    compute_loop_exit_candidates(
        cfg,
        &mut explored,
        &mut ordered_loops,
        &mut loop_exits,
        Vector::new(),
        src::BlockId::ZERO,
    );

    // Choose one candidate among the potential candidates.
    let mut exits: HashSet<src::BlockId::Id> = HashSet::new();
    let mut chosen_loop_exits: HashMap<src::BlockId::Id, Option<src::BlockId::Id>> = HashMap::new();
    // For every loop
    for loop_id in ordered_loops {
        // Check the candidates.
        // Ignore the candidates which have already been chosen as exits for other
        // loops (which should be outer loops).
        // We choose the exit with:
        // - the most occurrences
        // - the least total distance (if there are several possibilities)
        let mut current_exit: Option<src::BlockId::Id> = None;
        let mut occurrences = 0;
        let mut total_dist = std::usize::MAX;

        for (candidate_id, candidate_info) in loop_exits.get(&loop_id).unwrap().iter() {
            // Candidate already selected for another loop: ignore
            if exits.contains(candidate_id) {
                continue;
            }

            if candidate_info.occurrences.len() > occurrences {
                current_exit = Some(*candidate_id);
                occurrences = candidate_info.occurrences.len();
                total_dist = candidate_info.occurrences.iter().sum();
            } else if candidate_info.occurrences.len() > occurrences {
                let ntotal_dist = candidate_info.occurrences.iter().sum();
                if ntotal_dist > total_dist {
                    current_exit = Some(*candidate_id);
                    occurrences = candidate_info.occurrences.len();
                    total_dist = ntotal_dist;
                }
            }
        }

        // Register the exit
        match current_exit {
            None => {
                // No exit was found
                chosen_loop_exits.insert(loop_id, None);
            }
            Some(exit_id) => {
                exits.insert(exit_id);
                chosen_loop_exits.insert(loop_id, Some(exit_id));
            }
        }
    }

    // Return the chosen exits
    chosen_loop_exits
}

/// TODO: explanations
fn compute_switch_exits_explore(
    cfg: &CfgInfo,
    tsort_map: &HashMap<src::BlockId::Id, usize>,
    memoized: &mut HashMap<src::BlockId::Id, im::OrdSet<OrdBlockId>>,
    block_id: src::BlockId::Id,
) -> im::OrdSet<OrdBlockId> {
    // Shortcut
    match memoized.get(&block_id) {
        Some(res) => {
            return res.clone();
        }
        None => (),
    }

    // Find the next blocks, and their successors
    let children: Vec<src::BlockId::Id> = Vec::from_iter(cfg.cfg_no_be.neighbors(block_id));
    let mut children_succs: Vec<im::OrdSet<OrdBlockId>> = Vec::from_iter(
        children
            .iter()
            .map(|bid| compute_switch_exits_explore(cfg, tsort_map, memoized, *bid)),
    );

    // If there is exactly one child or less, it is trivial
    let succs = if children.len() == 0 {
        im::OrdSet::new()
    } else if children.len() == 1 {
        let child_id = children[0];
        let mut succs = children_succs.pop().unwrap();

        // Retrieve the rank, given by the topological order
        let child_rank = *tsort_map.get(&child_id).unwrap();
        let child_ord_block_id = OrdBlockId {
            id: child_id,
            rank: child_rank,
        };

        succs.insert(child_ord_block_id);
        succs
    }
    // Otherwise, there is a branching: we need to find the "best" minimal
    // successor, which allows to factorize the code as much as possible.
    // We do it in a very "brutal" manner:
    // - we look for the pair of children blocks which have the maximum
    //   intersection of successors.
    // - in this intersection, we take the first block id (remember we use
    //   topological sort), which will be our exit node.
    // Note that we're definitely not looking for performance here (and that
    // there shouldn't be too many blocks in a function body), but rather
    // quality of the generated code. If the following works well but proves
    // to be too slow, we'll think of a way of making it faster.
    // Note: another possibility would be to explore starting at the children
    // of the current node, and stop once two explorations lead to the same
    // block at some point: this should be the exit block.
    else {
        let mut max_inter_succs: im::OrdSet<OrdBlockId> = im::OrdSet::new();

        for i in 0..children_succs.len() {
            for j in (i + 1)..children_succs.len() {
                let i_succs = children_succs.get(i).unwrap().clone();
                let j_succs = children_succs.get(j).unwrap().clone();
                let inter_succs = i_succs.intersection(j_succs);

                if inter_succs.len() > max_inter_succs.len() {
                    max_inter_succs = inter_succs;
                }
            }
        }

        max_inter_succs
    };

    // Memoize
    memoized.insert(block_id, succs.clone());

    // Return
    succs
}

fn compute_switch_exits(
    cfg: &CfgInfo,
    tsort_map: &HashMap<src::BlockId::Id, usize>,
) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
    // Compute the filtered successors map, starting at the root node
    let mut fsuccs_map = HashMap::new();
    let _ = compute_switch_exits_explore(cfg, tsort_map, &mut fsuccs_map, src::BlockId::ZERO);

    // For every node which is a loop entry or a switch, retrieve the exit.
    // As the set of filtered successors is topologically sorted, the exit should be
    // the first node in the set (if the set is non empty)
    let mut exits = HashMap::new();
    for bid in cfg.loop_entries.iter().chain(cfg.switch_blocks.iter()) {
        let fsuccs = fsuccs_map.get(bid).unwrap();
        if fsuccs.is_empty() {
            exits.insert(*bid, None);
        } else {
            let exit = fsuccs.iter().next().unwrap();
            exits.insert(*bid, Some(exit.id));
        }
    }

    exits
}

fn compute_loop_switch_exits(
    cfg: &CfgInfo,
    // TODO: compute this one here
    tsort_map: &HashMap<src::BlockId::Id, usize>,
) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
    let mut loop_exits = compute_loop_exits(cfg);
    let switch_exits = compute_switch_exits(cfg, tsort_map);

    for (bid, exit_id) in switch_exits {
        // It is possible that a switch is actually a loop entry: *do not*
        // override the exit in this case
        if !loop_exits.contains_key(&bid) {
            loop_exits.insert(bid, exit_id);
        }
    }

    loop_exits
}

fn combine_statement_and_expression(
    statement: tgt::Statement,
    next_exp: Option<tgt::Expression>,
) -> tgt::Expression {
    let st = tgt::Expression::Statement(statement);
    match next_exp {
        Some(e) => tgt::Expression::Sequence(Box::new(st), Box::new(e)),
        None => st,
    }
}

fn combine_statements_and_expression(
    statements: Vec<tgt::Statement>,
    next: Option<tgt::Expression>,
) -> Option<tgt::Expression> {
    statements
        .into_iter()
        .rev()
        .fold(next, |e, st| Some(combine_statement_and_expression(st, e)))
}

fn get_goto_kind(
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: &Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    next_block_id: src::BlockId::Id,
) -> GotoKind {
    // First explore the parent loops in revert order
    let len = parent_loops.len();
    for i in 0..len {
        let loop_id = parent_loops.get(len - i - 1).unwrap();

        // If we goto a loop entry node: this is a 'continue'
        if next_block_id == *loop_id {
            return GotoKind::Continue(i);
        } else {
            // If we goto a loop exit node: this is a 'break'
            match exits_map.get(&loop_id).unwrap() {
                None => (),
                Some(exit_id) => {
                    if *exit_id == next_block_id {
                        return GotoKind::Break(i);
                    }
                }
            }
        }
    }

    // Check if the goto exits the current block
    if Some(next_block_id) == current_exit_block {
        return GotoKind::ExitBlock;
    }

    // Default
    return GotoKind::Goto;
}

enum GotoKind {
    Break(usize),
    Continue(usize),
    ExitBlock,
    Goto,
}

fn translate_child_expression(
    cfg: &CfgInfo,
    decl: &src::FunDecl,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    child_id: src::BlockId::Id,
) -> Option<tgt::Expression> {
    // Check if this is a backward call
    match get_goto_kind(exits_map, &parent_loops, current_exit_block, child_id) {
        GotoKind::Break(index) => Some(tgt::Expression::Statement(tgt::Statement::Break(index))),
        GotoKind::Continue(index) => {
            Some(tgt::Expression::Statement(tgt::Statement::Continue(index)))
        }
        // If we are going to an exit block we simply ignore the goto
        GotoKind::ExitBlock => None,
        GotoKind::Goto => {
            // "Standard" goto: just recursively translate
            translate_expression(
                cfg,
                decl,
                exits_map,
                parent_loops,
                current_exit_block,
                child_id,
            )
        }
    }
}

fn opt_expression_to_nop(opt_exp: Option<tgt::Expression>) -> tgt::Expression {
    match opt_exp {
        Some(exp) => exp,
        None => tgt::Expression::Statement(tgt::Statement::Nop),
    }
}

fn translate_statement(st: &src::Statement) -> Option<tgt::Statement> {
    match st {
        src::Statement::Assign(place, rvalue) => {
            Some(tgt::Statement::Assign(place.clone(), rvalue.clone()))
        }
        src::Statement::FakeRead(place) => Some(tgt::Statement::FakeRead(place.clone())),
        src::Statement::SetDiscriminant(place, variant_id) => {
            Some(tgt::Statement::SetDiscriminant(place.clone(), *variant_id))
        }
        src::Statement::StorageDead(_var_id) => None,
    }
}

fn translate_terminator(
    cfg: &CfgInfo,
    decl: &src::FunDecl,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    terminator: &src::Terminator,
) -> Option<tgt::Expression> {
    match terminator {
        src::Terminator::Panic | src::Terminator::Unreachable => {
            Some(tgt::Expression::Statement(tgt::Statement::Panic))
        }
        src::Terminator::Return => Some(tgt::Expression::Statement(tgt::Statement::Return)),
        src::Terminator::Goto { target } => translate_child_expression(
            cfg,
            decl,
            exits_map,
            parent_loops,
            current_exit_block,
            *target,
        ),
        src::Terminator::Drop { place, target } => {
            let opt_child = translate_child_expression(
                cfg,
                decl,
                exits_map,
                parent_loops,
                current_exit_block,
                *target,
            );
            let st = tgt::Statement::Drop(place.clone());
            Some(combine_statement_and_expression(st, opt_child))
        }
        src::Terminator::Call {
            func,
            region_params,
            type_params,
            args,
            dest,
            target,
        } => {
            let opt_child = translate_child_expression(
                cfg,
                decl,
                exits_map,
                parent_loops,
                current_exit_block,
                *target,
            );
            let st = tgt::Statement::Call(tgt::Call {
                func: func.clone(),
                region_params: region_params.clone(),
                type_params: type_params.clone(),
                args: args.clone(),
                dest: dest.clone(),
            });
            Some(combine_statement_and_expression(st, opt_child))
        }
        src::Terminator::Assert {
            cond,
            expected,
            target,
        } => {
            let opt_child = translate_child_expression(
                cfg,
                decl,
                exits_map,
                parent_loops,
                current_exit_block,
                *target,
            );
            let st = tgt::Statement::Assert(tgt::Assert {
                cond: cond.clone(),
                expected: *expected,
            });
            Some(combine_statement_and_expression(st, opt_child))
        }
        src::Terminator::Switch { discr, targets } => {
            // Translate the target expressions
            let targets = match &targets {
                src::SwitchTargets::If(then_tgt, else_tgt) => {
                    // Translate the children expressions
                    let then_exp = translate_child_expression(
                        cfg,
                        decl,
                        exits_map,
                        parent_loops.clone(),
                        current_exit_block,
                        *then_tgt,
                    );
                    let then_exp = opt_expression_to_nop(then_exp);
                    let else_exp = translate_child_expression(
                        cfg,
                        decl,
                        exits_map,
                        parent_loops.clone(),
                        current_exit_block,
                        *else_tgt,
                    );
                    let else_exp = opt_expression_to_nop(else_exp);

                    // Translate
                    tgt::SwitchTargets::If(Box::new(then_exp), Box::new(else_exp))
                }
                src::SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    // Translate the children expressions
                    let targets_exps = LinkedHashMap::from_iter(targets.iter().map(|(v, bid)| {
                        let exp = translate_child_expression(
                            cfg,
                            decl,
                            exits_map,
                            parent_loops.clone(),
                            current_exit_block,
                            *bid,
                        );
                        let exp = opt_expression_to_nop(exp);
                        (*v, exp)
                    }));

                    let otherwise_exp = translate_child_expression(
                        cfg,
                        decl,
                        exits_map,
                        parent_loops.clone(),
                        current_exit_block,
                        *otherwise,
                    );
                    let otherwise_exp = opt_expression_to_nop(otherwise_exp);

                    // Translate
                    tgt::SwitchTargets::SwitchInt(*int_ty, targets_exps, Box::new(otherwise_exp))
                }
            };

            // Return
            Some(tgt::Expression::Switch(discr.clone(), targets))
        }
    }
}

fn combine_expressions(
    exp1: Option<tgt::Expression>,
    exp2: Option<tgt::Expression>,
) -> Option<tgt::Expression> {
    match exp1 {
        None => exp2,
        Some(exp1) => match exp2 {
            None => Some(exp1),
            Some(exp2) => Some(tgt::Expression::Sequence(Box::new(exp1), Box::new(exp2))),
        },
    }
}

fn is_terminal(exp: &tgt::Expression) -> bool {
    is_terminal_explore(0, exp)
}

/// Return `true` if whatever the path we take, evaluating the expression
/// necessarily leads to:
/// - a panic or return
/// - a break which goes to a loop outside the expression
/// - a continue statement
fn is_terminal_explore(num_loops: usize, exp: &tgt::Expression) -> bool {
    match exp {
        tgt::Expression::Statement(st) => match st {
            tgt::Statement::Assign(_, _)
            | tgt::Statement::FakeRead(_)
            | tgt::Statement::SetDiscriminant(_, _)
            | tgt::Statement::Drop(_)
            | tgt::Statement::Assert(_)
            | tgt::Statement::Call(_)
            | tgt::Statement::Nop => false,
            tgt::Statement::Panic | tgt::Statement::Return => true,
            tgt::Statement::Break(index) => *index >= num_loops,
            tgt::Statement::Continue(_index) => true,
        },
        tgt::Expression::Sequence(exp1, exp2) => {
            if is_terminal_explore(num_loops, exp1) {
                return true;
            } else {
                return is_terminal_explore(num_loops, exp2);
            }
        }
        tgt::Expression::Switch(_, targets) => targets
            .get_targets()
            .iter()
            .all(|tgt_exp| is_terminal_explore(num_loops, tgt_exp)),
        tgt::Expression::Loop(loop_exp) => {
            return is_terminal_explore(num_loops + 1, loop_exp);
        }
    }
}

fn translate_expression(
    cfg: &CfgInfo,
    decl: &src::FunDecl,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    block_id: src::BlockId::Id,
) -> Option<tgt::Expression> {
    let block = decl.body.get(block_id).unwrap();

    // Check if we enter a loop: if so, update parent_loops and the current_exit_block
    let is_loop = cfg.loop_entries.contains(&block_id);
    let nparent_loops = if cfg.loop_entries.contains(&block_id) {
        let mut nparent_loops = parent_loops.clone();
        nparent_loops.push_back(block_id);
        nparent_loops
    } else {
        parent_loops.clone()
    };

    // If we enter a switch or a loop, we need to update the current_exit_block
    let is_switch = block.terminator.is_switch();
    let ncurrent_exit_block = if is_loop || is_switch {
        *exits_map.get(&block_id).unwrap()
    } else {
        current_exit_block
    };

    // Translate the terminator and the subsequent blocks
    let terminator = translate_terminator(
        cfg,
        decl,
        exits_map,
        nparent_loops,
        ncurrent_exit_block,
        &block.terminator,
    );

    // Translate the statements
    let statements = Vec::from_iter(
        block
            .statements
            .iter()
            .filter_map(|st| translate_statement(st)),
    );

    // We do different things if this is a loop, a switch (which is not
    // a loop) or something else.
    // Note that we need to do different treatments, because we don't
    // concatenate the exit block the same way for loops and switches.
    // In particular, for switches, we have to make sure we concatenate
    // the exit block *before* concatenating the statements preceding
    // the terminator, in order to avoid generating code of the form:
    // ```
    // e_prev; (s1; ...: sn; switch ...); e_switch_exit
    // ```
    if is_loop {
        // Put the statements and the terminator together
        let exp = combine_statements_and_expression(statements, terminator);

        // Put the whole loop body inside a `Loop` wrapper
        let exp = tgt::Expression::Loop(Box::new(exp.unwrap()));

        // Add the exit block
        let exp = if ncurrent_exit_block.is_some() {
            let exit_block_id = ncurrent_exit_block.unwrap();
            let next_exp = translate_expression(
                cfg,
                decl,
                exits_map,
                parent_loops,
                current_exit_block,
                exit_block_id,
            );
            combine_expressions(Some(exp), next_exp)
        } else {
            Some(exp)
        };

        exp
    } else if is_switch {
        // Use the terminator
        let exp = terminator.unwrap();

        // Concatenate the exit expression, if needs be
        let exp = if ncurrent_exit_block.is_some() && !is_terminal(&exp) {
            let exit_block_id = ncurrent_exit_block.unwrap();
            let next_exp = translate_expression(
                cfg,
                decl,
                exits_map,
                parent_loops,
                current_exit_block,
                exit_block_id,
            );
            combine_expressions(Some(exp), next_exp)
        } else {
            Some(exp)
        };

        // Concatenate the statements
        combine_statements_and_expression(statements, exp)
    } else {
        // Simply concatenate the statements and the terminator
        combine_statements_and_expression(statements, terminator)
    }
}

fn translate_function(im_ctx: &FunTransContext, src_decl_id: DefId::Id) -> tgt::FunDecl {
    // Retrieve the function declaration
    let src_decl = im_ctx.decls.get(src_decl_id).unwrap();

    // Explore the function body to create the control-flow graph without backward
    // edges, and identify the loop entries (which are destinations of backward edges).
    let cfg_info = build_cfg_partial_info(src_decl);
    let cfg_info = compute_cfg_info_from_partial(cfg_info);

    // Use the CFG without backward edges to topologically sort the nodes.
    // Note that `toposort` returns `Err` if and only if it finds cycles (which
    // can't happen).
    let tsorted: Vec<src::BlockId::Id> = toposort(&cfg_info.cfg_no_be, None).unwrap();

    // Build the map: block id -> topological sort rank
    let tsort_map: HashMap<src::BlockId::Id, usize> = HashMap::from_iter(
        tsorted
            .into_iter()
            .enumerate()
            .map(|(i, block_id)| (block_id, i)),
    );

    // Find the exit block for all the loops and switches, if such an exit point
    // exists.
    let exits_map = compute_loop_switch_exits(&cfg_info, &tsort_map);

    // Translate the body by reconstructing the loops and the conditional branchings.
    // Note that we shouldn't get `None`.
    let body_exp = translate_expression(
        &cfg_info,
        &src_decl,
        &exits_map,
        Vector::new(),
        None,
        src::BlockId::ZERO,
    )
    .unwrap();

    // Return the translated declaration
    tgt::FunDecl {
        def_id: src_decl.def_id,
        name: src_decl.name.clone(),
        signature: src_decl.signature.clone(),
        divergent: src_decl.divergent,
        arg_count: src_decl.arg_count,
        locals: src_decl.locals.clone(),
        body: body_exp,
    }
}

pub fn translate_functions(im_ctx: &FunTransContext) -> Decls {
    let mut out_decls = DefId::Vector::new();

    // Tranlsate the bodies one at a time
    for src_decl_id in im_ctx.decls.iter_indices() {
        out_decls.push_back(translate_function(im_ctx, src_decl_id));
    }

    // Print the functions
    for decl in &out_decls {
        trace!(
            "# Signature:\n{}\n\n# Function definition:\n{}\n",
            decl.signature.fmt_with_decls(&im_ctx.tt_ctx.types),
            decl.fmt_with_decls(&im_ctx.tt_ctx.types, &out_decls)
        );
    }

    out_decls
}
