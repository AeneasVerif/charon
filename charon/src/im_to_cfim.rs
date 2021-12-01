//! IM to CFIM (Control-Flow Internal MIR)
//!
//! The reconstruction algorithm is not written to be efficient (its complexity
//! is probably very bad), but it was not written to be: this is still an early
//! stage and we want the algorithm to generate the best reconstruction as
//! possible. We still need to test the algorithm on more interesting examples,
//! and will consider making it more efficient once it is a bit mature and well
//! tested.
//! Also note that we more importantly focus on making the algorithm sound: the
//! reconstructed program must always be equivalent to the original MIR program,
//! and the fact that the reconstruction preserves this property must be obvious.
//!
//! Finally, we conjecture the execution time shouldn't be too much a problem:
//! we don't expect the translation mechanism to be applied on super huge functions
//! (which will be difficult to formally analyze), and the MIR graphs are actually
//! not that big because statements are grouped into code blocks (a block is made
//! of a list of statements, followed by a terminator - branchings and jumps can
//! only be performed by terminators -, meaning that MIR graphs don't have that many
//! nodes and edges).

use crate::cfim_ast as tgt;
use crate::im_ast as src;
use crate::translate_functions_to_im::FunTransContext;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use im;
use im::Vector;
use petgraph::algo::dominators::simple_fast;
use petgraph::algo::floyd_warshall::floyd_warshall;
use petgraph::algo::toposort;
use petgraph::graphmap::DiGraphMap;
use petgraph::Direction;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::FromIterator;

pub type Defs = tgt::FunDefs;

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId::Id, ()>;

fn get_block_targets(def: &src::FunDef, block_id: src::BlockId::Id) -> Vec<src::BlockId::Id> {
    let block = def.body.get(block_id).unwrap();

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
    /// The reachability matrix:
    /// src can reach dest <==> (src, dest) in reachability
    /// TODO: this is not necessary anymore. There is a place where we use it
    /// as a test to shortcut some computations, but computing this matrix
    /// is actually probably too expensive for the shortcut to be useful...
    pub reachability: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
    /// Dominators (on the CFG *without* back-edges):
    /// n dominated by n' <==> (n, n') in dominated
    /// TODO: this is not used.
    pub dominated_no_be: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
}

/// Build the CFGs (the "regular" CFG and the CFG without backward edges) and
/// compute some information like the loop entries and the switch blocks.
fn build_cfg_partial_info(def: &src::FunDef) -> CfgPartialInfo {
    let mut cfg = CfgPartialInfo {
        cfg: Cfg::new(),
        cfg_no_be: Cfg::new(),
        loop_entries: HashSet::new(),
        backward_edges: HashSet::new(),
        switch_blocks: HashSet::new(),
    };

    // Add the nodes
    for block_id in def.body.iter_indices() {
        cfg.cfg.add_node(block_id);
        cfg.cfg_no_be.add_node(block_id);
    }

    // Add the edges
    let ancestors = im::HashSet::new();
    let mut explored = im::HashSet::new();
    build_cfg_partial_info_edges(&mut cfg, &ancestors, &mut explored, def, src::BlockId::ZERO);

    cfg
}

fn block_is_switch(def: &src::FunDef, block_id: src::BlockId::Id) -> bool {
    let block = def.body.get(block_id).unwrap();
    block.terminator.is_switch()
}

fn build_cfg_partial_info_edges(
    cfg: &mut CfgPartialInfo,
    ancestors: &im::HashSet<src::BlockId::Id>,
    explored: &mut im::HashSet<src::BlockId::Id>,
    def: &src::FunDef,
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
    if block_is_switch(def, block_id) {
        cfg.switch_blocks.insert(block_id);
    }

    // Retrieve the block targets
    let targets = get_block_targets(def, block_id);

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
            build_cfg_partial_info_edges(cfg, &ancestors, explored, def, *tgt);
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
    ///
    /// Note that it *may* happen that we have several exit candidates referenced
    /// more than once for one loop. This comes from the fact that whenever we
    /// reach a node from which the loop entry is not reachable (without using a
    /// backward edge leading to an outer loop entry), we register this node
    /// as well as all its children as exit candidates.
    /// Consider the following example:
    /// ```
    /// while i < max {
    ///     if cond {
    ///         break;
    ///     }
    ///     s += i;
    ///     i += 1
    /// }
    /// // All the below nodes are exit candidates (each of them is referenced twice)
    /// s += 1;
    /// return s;
    /// ```
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
fn loop_entry_is_reachable_from_inner(
    cfg: &CfgInfo,
    loop_entry: src::BlockId::Id,
    block_id: src::BlockId::Id,
) -> bool {
    // Shortcut: the loop entry is not reachable at all
    if !cfg.reachability.contains(&(block_id, loop_entry)) {
        return false;
    }

    // It is reachable in the complete graph. Check if it is reachable by not
    // going through backward edges which go to outer loops. In practice, we
    // just need to forbid the use of any backward edges at the exception of
    // those which go directly to the current loop's entry. This means that we
    // ignore backward edges to outer loops of course, but also backward edges
    // to inner loops because we shouldn't need to follow those (there should be
    // more direct paths).

    // Explore the graph starting at block_id
    let mut explored: HashSet<src::BlockId::Id> = HashSet::new();
    let mut stack: VecDeque<src::BlockId::Id> = VecDeque::new();
    stack.push_back(block_id);
    while !stack.is_empty() {
        let bid = stack.pop_front().unwrap();
        if explored.contains(&bid) {
            continue;
        }
        explored.insert(bid);

        let next_ids = cfg.cfg.neighbors_directed(bid, Direction::Outgoing);
        for next_id in next_ids {
            // Check if this is a backward edge
            if cfg.backward_edges.contains(&(bid, next_id)) {
                // Backward edge: only allow those going directly to the current
                // loop's entry
                if next_id == loop_entry {
                    // The loop entry is reachable
                    return true;
                } else {
                    // Forbidden edge: ignore
                    continue;
                }
            } else {
                // Nothing special: add the node to the stack for further
                // exploration
                stack.push_back(next_id);
            }
        }
    }

    // The loop entry is not reachable
    return false;
}

struct FilteredLoopParents {
    remaining_parents: Vector<(src::BlockId::Id, usize)>,
    removed_parents: Vector<(src::BlockId::Id, usize)>,
}

fn filter_loop_parents(
    cfg: &CfgInfo,
    parent_loops: &Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) -> Option<FilteredLoopParents> {
    let mut eliminate: usize = 0;
    for (loop_id, _ldist) in parent_loops.iter().rev() {
        if !loop_entry_is_reachable_from_inner(cfg, *loop_id, block_id) {
            eliminate += 1;
        } else {
            break;
        }
    }

    if eliminate > 0 {
        // Split the vector of parents
        let (mut remaining_parents, removed_parents) = parent_loops
            .clone()
            .split_at(parent_loops.len() - eliminate);
        //        let removed_parents = Vector::from_iter(removed_parents.into_iter().map(|(bid, _)| bid));

        // Update the distance to the last loop - we just increment the distance
        // by 1, because from the point of view of the parent loop, we just exited
        // a block and go to the next sequence of instructions.
        if !remaining_parents.is_empty() {
            remaining_parents
                .get_mut(remaining_parents.len() - 1)
                .unwrap()
                .1 += 1;
        }

        Some(FilteredLoopParents {
            remaining_parents,
            removed_parents,
        })
    } else {
        None
    }
}

/// List the nodes reachable from a starting point.
/// We list the nodes and the depth (in the AST) at which they were found.
fn list_reachable(cfg: &Cfg, start: src::BlockId::Id) -> HashMap<src::BlockId::Id, usize> {
    let mut reachable: HashMap<src::BlockId::Id, usize> = HashMap::new();
    let mut stack: VecDeque<(src::BlockId::Id, usize)> = VecDeque::new();
    stack.push_back((start, 0));

    while !stack.is_empty() {
        let (bid, dist) = stack.pop_front().unwrap();

        // Ignore this node if we already registered it with a better distance
        match reachable.get(&bid) {
            None => (),
            Some(original_dist) => {
                if *original_dist < dist {
                    continue;
                }
            }
        }

        // Inset the node with its distance
        reachable.insert(bid, dist);

        // Add the children to the stack
        for child in cfg.neighbors(bid) {
            stack.push_back((child, dist + 1));
        }
    }

    // Return
    return reachable;
}

/// Register a node and its children as exit candidates for a list of
/// parent loops.
fn register_children_as_loop_exit_candidates(
    cfg: &CfgInfo,
    loop_exits: &mut HashMap<src::BlockId::Id, HashMap<src::BlockId::Id, LoopExitCandidateInfo>>,
    removed_parent_loops: &Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) {
    // List the reachable nodes
    let reachable = list_reachable(&cfg.cfg_no_be, block_id);

    let mut base_dist = 0;
    // For every parent loop, in reverse order (we go from last to first in
    // order to correctly compute the distances)
    for (loop_id, loop_dist) in removed_parent_loops.iter().rev() {
        // Update the distance to the loop entry
        base_dist += *loop_dist;

        // Retrieve the candidates
        let candidates = loop_exits.get_mut(loop_id).unwrap();

        // Update them
        for (bid, dist) in reachable.iter() {
            let distance = base_dist + *dist;
            match candidates.get_mut(bid) {
                None => {
                    candidates.insert(
                        *bid,
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
                // We filtered some parent loops: it means this child and its
                // children are loop exit candidates for all those loops: we must
                // thus register them.
                // Note that we register the child *and* its children: the reason
                // is that we might do something *then* actually jump to the exit.
                // For instance, the following block of code:
                // ```
                // if cond { break; } else { ... }
                // ```
                //
                // Gets translated in MIR to something like this:
                // ```
                // bb1: {
                //   if cond -> bb2 else -> bb3; // bb2 is not the real exit
                // }
                //
                // bb2: {
                //   goto bb4; // bb4 is the real exit
                // }
                // ```
                register_children_as_loop_exit_candidates(
                    cfg,
                    loop_exits,
                    &fparent_loops.removed_parents,
                    child,
                );

                // Explore, with the filtered parents
                compute_loop_exit_candidates(
                    cfg,
                    explored,
                    ordered_loops,
                    loop_exits,
                    fparent_loops.remaining_parents,
                    child,
                );
            }
        }
    }
}

/// See [`compute_loop_switch_exits`](compute_loop_switch_exits) for
/// explanations about what "exits" are.
///
/// The following function computes the loop exits. It acts as follows.
///
/// We keep track of a stack of the loops in which we entered.
/// It is very easy to check when we enter a loop: loop entries are destinations
/// of backward edges, which can be spotted with a simple graph exploration (see
/// [`build_cfg_partial_info`](build_cfg_partial_info).
/// The criteria to consider whether we exit a loop is the following:
/// - we exit a loop if we go to a block from which we can't reach the loop
///   entry at all
/// - or if we can reach the loop entry, but must use a backward edge which goes
///   to an outer loop
///
/// It is better explained on the following example:
/// ```
/// 'outer while i < max {
///     'inner while j < max {
///        j += 1;
///     }
///     // (i)
///     i += 1;
/// }
/// ```
/// If we enter the inner loop then go to (i) from the inner loop, we consider
/// that we exited the outer loop because:
/// - we can reach the entry of the inner loop from (i) (by finishing then
///   starting again an iteration of the outer loop)
/// - but doing this requires taking a backward edge which goes to the outer loop
///
/// Whenever we exit a loop, we save the block we went to as an exit candidate
/// for this loop. Note that there may by many exit candidates. For instance,
/// in the below example:
/// ```
/// while ... {
///    ...
///    if ... {
///        // We can't reach the loop entry from here: this is an exit
///        // candidate
///        return;
///    }
/// }
/// // This is another exit candidate - and this is the one we want to use
/// // as the "real" exit...
/// ...
/// ```
///
/// Also note that it may happen that we go several times to the same exit (if
/// we use breaks for instance): we record the number of times an exit candidate
/// is used.
///
/// Once we listed all the exit candidates, we find the "best" one for every
/// loop, starting with the outer loops. We start with outer loops because
/// inner loops might use breaks to exit to the exit of outer loops: if we
/// start with the inner loops, the exit which is "natural" for the outer loop
/// might end up being used for one of the inner loops...
///
/// The best exit is the following one:
/// - it is the one which is used the most times (actually, there should be
///   at most one candidate which is referenced strictly more than once)
/// - if several exits have the same number of occurrences, we choose the one
///   for which we goto the "earliest" (earliest meaning that the goto is close to
///   the loop entry node in the AST). The reason is that all the loops should
///   have an outer if ... then ... else ... which executes the loop body or goes
///   to the exit (note that this is not necessarily the first
///   if ... then ... else ... we find: loop conditions can be arbitrary
///   expressions, containing branchings).
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

    {
        // Debugging
        let candidates: Vec<String> = loop_exits
            .iter()
            .map(|(loop_id, candidates)| format!("{} -> {:?}", loop_id, candidates))
            .collect();
        trace!("Loop exit candidates:\n{}", candidates.join("\n"));
    }

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

        // First:
        // - filter the candidates
        // - compute the number of occurrences
        // - compute the sum of distances
        let loop_exits = Vec::from_iter(loop_exits.get(&loop_id).unwrap().iter().filter_map(
            |(candidate_id, candidate_info)| {
                // If candidate already selected for another loop: ignore
                if exits.contains(candidate_id) {
                    None
                } else {
                    let num_occurrences = candidate_info.occurrences.len();
                    let dist_sum = candidate_info.occurrences.iter().sum();
                    Some((*candidate_id, num_occurrences, dist_sum))
                }
            },
        ));

        // Second: actually select the proper candidate
        let mut best_exit: Option<src::BlockId::Id> = None;
        let mut best_occurrences = 0;
        let mut best_dist_sum = std::usize::MAX;

        for (candidate_id, occurrences, dist_sum) in loop_exits.iter() {
            if (*occurrences > best_occurrences)
                || (*occurrences == best_occurrences && *dist_sum < best_dist_sum)
            {
                best_exit = Some(*candidate_id);
                best_occurrences = *occurrences;
                best_dist_sum = *dist_sum;
            }
        }

        // Sanity check: there are no two different candidates with exactly the
        // same number of occurrences and dist sum (if it is the case, the exit
        // node will not be deterministically chosen, which is a problem because
        // the reconstruction algorithm is then non-deterministic).
        let num_possible_candidates = loop_exits
            .iter()
            .filter(|(_, occs, dsum)| *occs == best_occurrences && *dsum == best_dist_sum)
            .count();
        assert!(num_possible_candidates <= 1);

        // Register the exit
        match best_exit {
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
    trace!("Chosen loop exits: {:?}", chosen_loop_exits);
    chosen_loop_exits
}

fn compute_switch_exits_explore(
    cfg: &CfgInfo,
    tsort_map: &HashMap<src::BlockId::Id, usize>,
    loop_exits: &HashSet<src::BlockId::Id>,
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
            .map(|bid| compute_switch_exits_explore(cfg, tsort_map, loop_exits, memoized, *bid)),
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
    // Note: actually, we could look only for *any* two pair of children
    // whose successors intersection is non empty: I think it works in the
    // general case.
    else {
        let mut max_inter_succs: im::OrdSet<OrdBlockId> = im::OrdSet::new();

        for i in 0..children_succs.len() {
            for j in (i + 1)..children_succs.len() {
                let i_succs = children_succs.get(i).unwrap().clone();
                let j_succs = children_succs.get(j).unwrap().clone();
                let inter_succs = i_succs.intersection(j_succs);

                if inter_succs.len() > max_inter_succs.len() {
                    // As the set of filtered successors is topologically sorted,
                    // the exit should be the first node in the set (the set is
                    // necessarily non empty).
                    // We ignore candidates where the exit is actually a loop
                    // exit (it can happen, if two branches of an if call end
                    // with a `break` for instance).
                    let exit = inter_succs.iter().next().unwrap();
                    if !loop_exits.contains(&exit.id) {
                        max_inter_succs = inter_succs;
                    }
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

/// See [`compute_loop_switch_exits`](compute_loop_switch_exits) for
/// explanations about what "exits" are.
///
/// In order to compute the switch exits, we simply recursively compute a
/// topologically ordered set of "filtered successors" as follows (note
/// that we work in the CFG *without* back edges):
/// - for a block which doesn't branch (only one successor), the filtered
///   successors are the filtered sucessors of the successor, plus the
///   successor itself
/// - for a block which branches, we compute the filtered successors of
///   all the successors (i.e, all the branches), and find the "best"
///   intersection of successors.
///   Note that we find the "best" intersection (a pair of branches which
///   maximize the intersection of filtered successors) because some branches
///   might never join the control-flow of the other branches, if they contain
///   a `break`, `return`, `panic`, etc., like here:
///   ```
///   if b { x = 3; } { return; }
///   y += x;
///   ...
///   ```
fn compute_switch_exits(
    cfg: &CfgInfo,
    tsort_map: &HashMap<src::BlockId::Id, usize>,
    loop_exits: &HashSet<src::BlockId::Id>,
) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
    // Compute the filtered successors map, starting at the root node
    let mut fsuccs_map = HashMap::new();
    let _ = compute_switch_exits_explore(
        cfg,
        tsort_map,
        loop_exits,
        &mut fsuccs_map,
        src::BlockId::ZERO,
    );

    // For every node which is a switch, retrieve the exit.
    // As the set of filtered successors is topologically sorted, the exit should be
    // the first node in the set (if the set is non empty)
    let mut exits = HashMap::new();
    for bid in cfg.switch_blocks.iter() {
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

/// Compute the exits for the loops and the switches (switch on integer and
/// if ... then ... else ...). We need to do this because control-flow in MIR
/// is destructured: we have gotos everywhere.
///
/// Let's consider the following piece of code:
/// ```
/// if cond1 { ... } else { ... };
/// if cond2 { ... } else { ... };
/// ```
/// Once converted to MIR, the control-flow is destructured, which means we
/// have gotos everywhere. When reconstructing the control-flow, we have
/// to be careful about the point where we should join the two branches of
/// the first if.
/// For instance, if we don't notice they should be joined at some point (i.e,
/// whatever the branch we take, there is a moment when we go to the exact
/// same place, just before the second if), we might generate code like
/// this, with some duplicata:
/// ```
/// if cond1 { ...; if cond2 { ... } else { ...} }
/// else { ...; if cond2 { ... } else { ...} }
/// ```
///
/// Such a reconstructed program is valid, but it is definitely non-optimal:
/// it is very different from the original program (making it less clean and
/// clear), more bloated, and might involve duplicating the proof effort.
///
/// For this reason, we need to find the "exit" of the first loop, which is
/// the point where the two branches join. Note that this can be a bit tricky,
/// because there may be more than two branches (if we do `switch(x) { ... }`),
/// and some of them might not join (if they contain a `break`, `panic`,
/// `return`, etc.).
///
/// Finally, some similar issues arise for loops. For instance, let's consider
/// the following piece of code:
/// ```
/// while cond1 {
///   e1;
///   if cond2 {
///     break;
///   }
///   e2;
/// }
/// e3;
/// return;
/// ```
///
/// Note that in MIR, the loop gets desugared to an if ... then ... else ....
/// From the MIR, We want to generate something like this:
/// ```
/// loop {
///   if cond1 {
///     e1;
///     if cond2 {
///       break;
///     }
///     e2;
///     continue;
///   }
///   else {
///     break;
///   }
/// };
/// e3;
/// return;
/// ```
///
/// But if we don't pay attention, we might end up with that, once again with
/// duplications:
/// ```
/// loop {
///   if cond1 {
///     e1;
///     if cond2 {
///       e3;
///       return;
///     }
///     e2;
///     continue;
///   }
///   else {
///     e3;
///     return;
///   }
/// }
/// ```
/// We thus have to notice that if the loop condition is false, we goto the same
/// block as when following the goto introduced by the break inside the loop, and
/// this block is dubbed the "loop exit".
///
/// The following function thus computes the "exits" for loops and switches, which
/// are basically the points where control-flow joins.
fn compute_loop_switch_exits(
    cfg_info: &CfgInfo,
) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
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

    // Compute the loop exits
    let mut loop_exits = compute_loop_exits(cfg_info);

    // Compute the switch exits
    let loop_exits_set: HashSet<src::BlockId::Id> =
        HashSet::from_iter(loop_exits.iter().filter_map(|(_, bid)| *bid));
    let switch_exits = compute_switch_exits(cfg_info, &tsort_map, &loop_exits_set);

    // Put all this together
    for (bid, exit_id) in switch_exits {
        // It is possible that a switch is actually a loop entry: *do not*
        // override the exit in this case.
        if !loop_exits.contains_key(&bid) {
            // Also, we ignore switch exits which are actually loop exits.
            // Note that doing this shouldn't be necessary, because we actually
            // don't consider switch exit candidates which are loop exits, but
            // this may change.
            match exit_id {
                None => {
                    let _ = loop_exits.insert(bid, None);
                }
                Some(exit_id) => {
                    if !loop_exits_set.contains(&exit_id) {
                        loop_exits.insert(bid, Some(exit_id));
                    }
                }
            }
        }
    }

    loop_exits
}

fn combine_statement_and_statement(
    statement: tgt::Statement,
    next_st: Option<tgt::Statement>,
) -> tgt::Statement {
    match next_st {
        Some(next_st) => tgt::Statement::Sequence(Box::new(statement), Box::new(next_st)),
        None => statement,
    }
}

fn combine_statements_and_statement(
    statements: Vec<tgt::Statement>,
    next: Option<tgt::Statement>,
) -> Option<tgt::Statement> {
    statements.into_iter().rev().fold(next, |seq, st| {
        Some(combine_statement_and_statement(st, seq))
    })
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

fn translate_child_block(
    cfg: &CfgInfo,
    def: &src::FunDef,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    explored: &mut HashSet<src::BlockId::Id>,
    child_id: src::BlockId::Id,
) -> Option<tgt::Statement> {
    // Check if this is a backward call
    match get_goto_kind(exits_map, &parent_loops, current_exit_block, child_id) {
        GotoKind::Break(index) => Some(tgt::Statement::Break(index)),
        GotoKind::Continue(index) => Some(tgt::Statement::Continue(index)),
        // If we are going to an exit block we simply ignore the goto
        GotoKind::ExitBlock => None,
        GotoKind::Goto => {
            // "Standard" goto: just recursively translate
            translate_block(
                cfg,
                def,
                exits_map,
                parent_loops,
                current_exit_block,
                explored,
                child_id,
            )
        }
    }
}

fn opt_statement_to_nop_if_none(opt_st: Option<tgt::Statement>) -> tgt::Statement {
    match opt_st {
        Some(st) => st,
        None => tgt::Statement::Nop,
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
    def: &src::FunDef,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    explored: &mut HashSet<src::BlockId::Id>,
    terminator: &src::Terminator,
) -> Option<tgt::Statement> {
    match terminator {
        src::Terminator::Panic | src::Terminator::Unreachable => Some(tgt::Statement::Panic),
        src::Terminator::Return => Some(tgt::Statement::Return),
        src::Terminator::Goto { target } => translate_child_block(
            cfg,
            def,
            exits_map,
            parent_loops,
            current_exit_block,
            explored,
            *target,
        ),
        src::Terminator::Drop { place, target } => {
            let opt_child = translate_child_block(
                cfg,
                def,
                exits_map,
                parent_loops,
                current_exit_block,
                explored,
                *target,
            );
            let st = tgt::Statement::Drop(place.clone());
            Some(combine_statement_and_statement(st, opt_child))
        }
        src::Terminator::Call {
            func,
            region_params,
            type_params,
            args,
            dest,
            target,
        } => {
            let opt_child = translate_child_block(
                cfg,
                def,
                exits_map,
                parent_loops,
                current_exit_block,
                explored,
                *target,
            );
            let st = tgt::Statement::Call(tgt::Call {
                func: func.clone(),
                region_params: region_params.clone(),
                type_params: type_params.clone(),
                args: args.clone(),
                dest: dest.clone(),
            });
            Some(combine_statement_and_statement(st, opt_child))
        }
        src::Terminator::Assert {
            cond,
            expected,
            target,
        } => {
            let opt_child = translate_child_block(
                cfg,
                def,
                exits_map,
                parent_loops,
                current_exit_block,
                explored,
                *target,
            );
            let st = tgt::Statement::Assert(tgt::Assert {
                cond: cond.clone(),
                expected: *expected,
            });
            Some(combine_statement_and_statement(st, opt_child))
        }
        src::Terminator::Switch { discr, targets } => {
            // Translate the target expressions
            let targets = match &targets {
                src::SwitchTargets::If(then_tgt, else_tgt) => {
                    // Translate the children expressions
                    let then_exp = translate_child_block(
                        cfg,
                        def,
                        exits_map,
                        parent_loops.clone(),
                        current_exit_block,
                        explored,
                        *then_tgt,
                    );
                    let then_exp = opt_statement_to_nop_if_none(then_exp);
                    let else_exp = translate_child_block(
                        cfg,
                        def,
                        exits_map,
                        parent_loops.clone(),
                        current_exit_block,
                        explored,
                        *else_tgt,
                    );
                    let else_exp = opt_statement_to_nop_if_none(else_exp);

                    // Translate
                    tgt::SwitchTargets::If(Box::new(then_exp), Box::new(else_exp))
                }
                src::SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    // Translate the children expressions
                    let targets_exps = LinkedHashMap::from_iter(targets.iter().map(|(v, bid)| {
                        let exp = translate_child_block(
                            cfg,
                            def,
                            exits_map,
                            parent_loops.clone(),
                            current_exit_block,
                            explored,
                            *bid,
                        );
                        let exp = opt_statement_to_nop_if_none(exp);
                        (*v, exp)
                    }));

                    let otherwise_exp = translate_child_block(
                        cfg,
                        def,
                        exits_map,
                        parent_loops.clone(),
                        current_exit_block,
                        explored,
                        *otherwise,
                    );
                    let otherwise_exp = opt_statement_to_nop_if_none(otherwise_exp);

                    // Translate
                    tgt::SwitchTargets::SwitchInt(*int_ty, targets_exps, Box::new(otherwise_exp))
                }
            };

            // Return
            Some(tgt::Statement::Switch(discr.clone(), targets))
        }
    }
}

fn combine_expressions(
    exp1: Option<tgt::Statement>,
    exp2: Option<tgt::Statement>,
) -> Option<tgt::Statement> {
    match exp1 {
        None => exp2,
        Some(exp1) => match exp2 {
            None => Some(exp1),
            Some(exp2) => Some(tgt::Statement::Sequence(Box::new(exp1), Box::new(exp2))),
        },
    }
}

fn is_terminal(exp: &tgt::Statement) -> bool {
    is_terminal_explore(0, exp)
}

/// Return `true` if whatever the path we take, evaluating the statement
/// necessarily leads to:
/// - a panic or return
/// - a break which goes to a loop outside the expression
/// - a continue statement
fn is_terminal_explore(num_loops: usize, st: &tgt::Statement) -> bool {
    match st {
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
        tgt::Statement::Sequence(st1, st2) => {
            if is_terminal_explore(num_loops, st1) {
                return true;
            } else {
                return is_terminal_explore(num_loops, st2);
            }
        }
        tgt::Statement::Switch(_, targets) => targets
            .get_targets()
            .iter()
            .all(|tgt_st| is_terminal_explore(num_loops, tgt_st)),
        tgt::Statement::Loop(loop_st) => {
            return is_terminal_explore(num_loops + 1, loop_st);
        }
    }
}

fn translate_block(
    cfg: &CfgInfo,
    def: &src::FunDef,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    explored: &mut HashSet<src::BlockId::Id>,
    block_id: src::BlockId::Id,
) -> Option<tgt::Statement> {
    // Check that we didn't already translate this block, and insert the block id
    // in the set of already translated blocks.
    // This is not necessary for the algorithm correctness. We enforce this only
    // to guarantee the quality of the translation: if a block gets translated
    // twice, it means we didn't correctly identify how to reconstruct the control-
    // flow, and that the reconstructed program contains duplicated pieces of code.
    // As this is still an early stage, we want to make sure we spot such
    // duplication, to update the reconstruction accordingly. In the future, we
    // might want to make this test optional, and let the user control its
    // activation.
    trace!("Parent loops: {:?}, Block id: {}", parent_loops, block_id);
    assert!(!explored.contains(&block_id));
    explored.insert(block_id);

    let block = def.body.get(block_id).unwrap();

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
        def,
        exits_map,
        nparent_loops,
        ncurrent_exit_block,
        explored,
        &block.terminator,
    );

    // Translate the statements inside the block
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
        let exp = combine_statements_and_statement(statements, terminator);

        // Put the whole loop body inside a `Loop` wrapper
        let exp = tgt::Statement::Loop(Box::new(exp.unwrap()));

        // Add the exit block
        let exp = if ncurrent_exit_block.is_some() {
            let exit_block_id = ncurrent_exit_block.unwrap();
            let next_exp = translate_block(
                cfg,
                def,
                exits_map,
                parent_loops,
                current_exit_block,
                explored,
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
        let exp = if ncurrent_exit_block.is_some() {
            // Sanity check: if there is an exit block, this block must be
            // reachable (i.e, there must exist a path in the switch which
            // doesn't end with `panic`, `return`, etc.).
            assert!(!is_terminal(&exp));

            let exit_block_id = ncurrent_exit_block.unwrap();
            let next_exp = translate_block(
                cfg,
                def,
                exits_map,
                parent_loops,
                current_exit_block,
                explored,
                exit_block_id,
            );
            combine_expressions(Some(exp), next_exp)
        } else {
            Some(exp)
        };

        // Concatenate the statements
        combine_statements_and_statement(statements, exp)
    } else {
        // Simply concatenate the statements and the terminator
        combine_statements_and_statement(statements, terminator)
    }
}

fn translate_function(im_ctx: &FunTransContext, src_def_id: FunDefId::Id) -> tgt::FunDef {
    // Retrieve the function definition
    let src_def = im_ctx.defs.get(src_def_id).unwrap();
    trace!("Reconstructing: {}", src_def.name);

    // Explore the function body to create the control-flow graph without backward
    // edges, and identify the loop entries (which are destinations of backward edges).
    let cfg_info = build_cfg_partial_info(src_def);
    let cfg_info = compute_cfg_info_from_partial(cfg_info);

    // Find the exit block for all the loops and switches, if such an exit point
    // exists.
    let exits_map = compute_loop_switch_exits(&cfg_info);

    // Translate the body by reconstructing the loops and the conditional branchings.
    // Note that we shouldn't get `None`.
    let body_exp = translate_block(
        &cfg_info,
        &src_def,
        &exits_map,
        Vector::new(),
        None,
        &mut HashSet::new(),
        src::BlockId::ZERO,
    )
    .unwrap();

    // Return the translated definition
    tgt::FunDef {
        def_id: src_def.def_id,
        name: src_def.name.clone(),
        signature: src_def.signature.clone(),
        divergent: src_def.divergent,
        arg_count: src_def.arg_count,
        locals: src_def.locals.clone(),
        body: body_exp,
    }
}

pub fn translate_functions(im_ctx: &FunTransContext) -> Defs {
    let mut out_defs = FunDefId::Vector::new();

    // Tranlsate the bodies one at a time
    for src_def_id in im_ctx.defs.iter_indices() {
        out_defs.push_back(translate_function(im_ctx, src_def_id));
    }

    // Print the functions
    for def in &out_defs {
        trace!(
            "# Signature:\n{}\n\n# Function definition:\n{}\n",
            def.signature.fmt_with_defs(&im_ctx.tt_ctx.types),
            def.fmt_with_defs(&im_ctx.tt_ctx.types, &out_defs)
        );
    }

    out_defs
}
