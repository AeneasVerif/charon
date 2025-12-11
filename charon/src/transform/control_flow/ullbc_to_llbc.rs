//! ULLBC to LLBC
//!
//! We reconstruct the control-flow in the Unstructured LLBC.
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
//! only be performed by terminators -, meaning that MIR graphs don't have that
//! many nodes and edges).

use indexmap::IndexMap;
use itertools::Itertools;
use petgraph::algo::dijkstra;
use petgraph::algo::dominators::{Dominators, simple_fast};
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::{Dfs, DfsPostOrder, GraphBase, IntoNeighbors, Visitable, Walker};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::mem;

use crate::common::ensure_sufficient_stack;
use crate::errors::sanity_check;
use crate::formatter::IntoFormatter;
use crate::ids::IndexVec;
use crate::llbc_ast as tgt;
use crate::meta::{Span, combine_span};
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;
use crate::transform::ctx::TransformPass;
use crate::ullbc_ast::{self as src, BlockId};
use crate::{ast::*, register_error};

/// Arbitrary-precision numbers
type BigUint = fraction::DynaInt<u64, fraction::BigUint>;
type BigRational = fraction::Ratio<BigUint>;

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId, ()>;

/// Information precomputed about a function's CFG.
#[derive(Debug)]
struct CfgInfo {
    /// The CFG
    pub cfg: Cfg,
    /// The CFG where all the backward edges have been removed. Aka "forward CFG".
    pub fwd_cfg: Cfg,
    /// We consider the destination of the backward edges to be loop entries and
    /// store them here.
    pub loop_entries: HashSet<src::BlockId>,
    /// The blocks whose terminators are a switch are stored here.
    pub switch_blocks: HashSet<src::BlockId>,
    /// Tree of which nodes dominates which other nodes.
    #[expect(unused)]
    pub dominator_tree: Dominators<BlockId>,
    /// Computed data about each block.
    pub block_data: IndexVec<BlockId, BlockData>,
}

#[derive(Debug)]
struct BlockData {
    pub id: BlockId,
    /// Order in a reverse postorder numbering. `None` if the block is unreachable.
    pub reverse_postorder: Option<u32>,
    /// Node from where we can only reach error nodes (panic, etc.)
    pub only_reach_error: bool,
    /// List of reachable nodes, with the length of shortest path to them. Includes the current
    /// node.
    pub shortest_paths: hashbrown::HashMap<BlockId, usize>,
    /// Let's say we put a quantity of water equal to 1 on the block, and the water flows downards.
    /// Whenever there is a branching, the quantity of water gets equally divided between the
    /// branches. When the control flows join, we put the water back together. The set below
    /// computes the amount of water received by each descendant of the node.
    ///
    /// TODO: there must be a known algorithm which computes this, right?...
    /// This is exactly this problems:
    /// <https://stackoverflow.com/questions/78221666/algorithm-for-total-flow-through-weighted-directed-acyclic-graph>
    /// TODO: the way I compute this is not efficient.
    pub flow: IndexVec<BlockId, BigRational>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct BlockWithRank<T> {
    /// A "rank" quantity that we use to order the nodes.
    /// By placing the `rank` field before the `id`, we make sure that
    /// we use the rank first in the lexicographic order.
    rank: T,
    id: src::BlockId,
}
type OrdBlockId = BlockWithRank<u32>;

/// Error indicating that the control-flow graph is not reducible. The contained block id is a
/// block involved in an irreducible subgraph.
struct Irreducible(BlockId);

impl CfgInfo {
    /// Build the CFGs (the "regular" CFG and the CFG without backward edges) and
    /// compute some information like the loop entries and the switch blocks.
    fn build(body: &src::BodyContents) -> Result<Self, Irreducible> {
        let start_block = BlockId::ZERO;

        // Build the node graph (we ignore unwind paths for now).
        let mut cfg = Cfg::new();
        for (block_id, block) in body.iter_indexed() {
            cfg.add_node(block_id);
            for tgt in block.targets_ignoring_unwind() {
                cfg.add_edge(block_id, tgt, ());
            }
        }

        let empty_flow = body.map_ref(|_| BigRational::new(0u64.into(), 1u64.into()));
        let mut block_data: IndexVec<BlockId, BlockData> =
            body.map_ref_indexed(|id, _| BlockData {
                id,
                // Default values will stay for unreachable nodes, which are irrelevant.
                reverse_postorder: None,
                only_reach_error: false,
                shortest_paths: Default::default(),
                flow: empty_flow.clone(),
            });

        // Compute the dominator tree.
        let dominator_tree = simple_fast(&cfg, start_block);

        // Compute reverse postorder numbering.
        for (i, block_id) in DfsPostOrder::new(&cfg, start_block).iter(&cfg).enumerate() {
            let rev_post_id = body.slot_count() - i;
            assert!(rev_post_id <= u32::MAX as usize);
            block_data[block_id].reverse_postorder = Some(rev_post_id as u32);
        }

        // Compute the forward graph (without backward edges).
        let mut fwd_cfg = Cfg::new();
        let mut loop_entries = HashSet::new();
        let mut switch_blocks = HashSet::new();
        for src in cfg.nodes() {
            if block_data[src].reverse_postorder.is_none() {
                // Unreachable block
                continue;
            }
            fwd_cfg.add_node(src);
            if body[src].terminator.kind.is_switch() {
                switch_blocks.insert(src);
            }
            for tgt in cfg.neighbors(src) {
                // Check if the edge is a backward edge.
                if block_data[src].reverse_postorder >= block_data[tgt].reverse_postorder {
                    // This is a backward edge
                    loop_entries.insert(tgt);
                    // A cfg is reducible iff the target of every back edge dominates the
                    // edge's source.
                    if !dominator_tree.dominators(src).unwrap().contains(&tgt) {
                        return Err(Irreducible(src));
                    }
                } else {
                    fwd_cfg.add_edge(src, tgt, ());
                }
            }
        }

        for block_id in DfsPostOrder::new(&fwd_cfg, start_block).iter(&fwd_cfg) {
            let block = &body[block_id];
            let targets = cfg.neighbors(block_id).collect_vec();
            let fwd_targets = fwd_cfg.neighbors(block_id).collect_vec();

            // Compute the nodes that can only reach error nodes.
            // The node can only reach error nodes if:
            // - it is an error node;
            // - or it has neighbors and they all lead to errors.
            // Note that if there is a backward edge, `only_reach_error` cannot contain this
            // node yet. In other words, this does not consider infinite loops as reaching an
            // error node.
            if block.terminator.is_error()
                || (!targets.is_empty()
                    && targets.iter().all(|&tgt| block_data[tgt].only_reach_error))
            {
                block_data[block_id].only_reach_error = true;
            }

            // Compute the flows between each pair of nodes.
            let mut flow: IndexVec<src::BlockId, BigRational> =
                mem::take(&mut block_data[block_id].flow);
            if !fwd_targets.is_empty() {
                // We need to divide the initial flow equally between the children
                let factor = BigRational::new(1u64.into(), fwd_targets.len().into());

                // For each child, multiply the flows of its own children by the ratio,
                // and add.
                for &child_id in &fwd_targets {
                    // First, add the child itself
                    flow[child_id] += factor.clone();

                    // Then add its successors
                    let child = &block_data[child_id];
                    for grandchild in child.reachable_excluding_self() {
                        // Flow from `child` to `grandchild`
                        let child_flow = child.flow[grandchild].clone();
                        flow[grandchild] += factor.clone() * child_flow;
                    }
                }
            }
            block_data[block_id].flow = flow;

            // Compute shortest paths to all reachable nodes in the forward graph.
            block_data[block_id].shortest_paths = dijkstra(&fwd_cfg, block_id, None, |_| 1usize);
        }

        Ok(CfgInfo {
            cfg,
            fwd_cfg,
            loop_entries,
            switch_blocks,
            dominator_tree,
            block_data,
        })
    }

    fn block_data(&self, block_id: BlockId) -> &BlockData {
        &self.block_data[block_id]
    }
    // fn can_reach(&self, src: BlockId, tgt: BlockId) -> bool {
    //     self.block_data[src].shortest_paths.contains_key(&tgt)
    // }
    fn topo_rank(&self, block_id: BlockId) -> u32 {
        self.block_data[block_id].reverse_postorder.unwrap()
    }
    /// Create an [OrdBlockId] from a block id and a rank given by a map giving
    /// a sort (topological in our use cases) over the graph.
    fn make_ord_block_id(&self, block_id: BlockId) -> OrdBlockId {
        OrdBlockId {
            id: block_id,
            rank: self.topo_rank(block_id),
        }
    }
    fn is_backward_edge(&self, src: BlockId, tgt: BlockId) -> bool {
        self.block_data[src].reverse_postorder >= self.block_data[tgt].reverse_postorder
            && self.cfg.contains_edge(src, tgt)
    }
}

impl BlockData {
    fn shortest_paths_including_self(&self) -> impl Iterator<Item = (BlockId, usize)> {
        self.shortest_paths.iter().map(|(bid, d)| (*bid, *d))
    }
    fn shortest_paths_excluding_self(&self) -> impl Iterator<Item = (BlockId, usize)> {
        self.shortest_paths_including_self()
            .filter(move |&(bid, _)| bid != self.id)
    }
    #[expect(unused)]
    fn reachable_including_self(&self) -> impl Iterator<Item = BlockId> {
        self.shortest_paths_including_self().map(|(bid, _)| bid)
    }
    fn reachable_excluding_self(&self) -> impl Iterator<Item = BlockId> {
        self.shortest_paths_excluding_self().map(|(bid, _)| bid)
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
    /// ```text
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

struct FilteredLoopParents {
    remaining_parents: Vec<(src::BlockId, usize)>,
    removed_parents: Vec<(src::BlockId, usize)>,
}

#[derive(Debug, Default, Clone)]
struct ExitInfo {
    is_loop_entry: bool,
    is_switch_entry: bool,
    /// The loop exit
    loop_exit: Option<src::BlockId>,
    /// Some loop exits actually belong to outer switches. We still need
    /// to track them in the loop exits, in order to know when we should
    /// insert a break. However, we need to make sure we don't add the
    /// corresponding block in a sequence, after having translated the
    /// loop, like so:
    /// ```text
    /// loop {
    ///   loop_body
    /// };
    /// exit_blocks // OK if the exit "belongs" to the loop
    /// ```
    ///
    /// In case the exit doesn't belong to the loop:
    /// ```text
    /// if b {
    ///   loop {
    ///     loop_body
    ///   } // no exit blocks after the loop
    /// }
    /// else {
    ///   ...
    /// };
    /// exit_blocks // the exit blocks are here
    /// ```
    owned_loop_exit: Option<src::BlockId>,
    /// The switch exit.
    /// Note that the switch exits are always owned.
    owned_switch_exit: Option<src::BlockId>,
}

/// The exits of a graph
#[derive(Debug, Clone)]
struct ExitsInfo {
    exits: IndexVec<BlockId, ExitInfo>,
}

impl ExitsInfo {
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
        loop_entry: src::BlockId,
        block_id: src::BlockId,
    ) -> bool {
        // It is reachable in the complete graph. Check if it is reachable by not
        // going through backward edges which go to outer loops. In practice, we
        // just need to forbid the use of any backward edges at the exception of
        // those which go directly to the current loop's entry. This means that we
        // ignore backward edges to outer loops of course, but also backward edges
        // to inner loops because we shouldn't need to follow those (there should be
        // more direct paths).
        Dfs::new(&cfg.fwd_cfg, block_id)
            .iter(&cfg.fwd_cfg)
            .any(|bid| cfg.is_backward_edge(bid, loop_entry))
    }

    fn filter_loop_parents(
        cfg: &CfgInfo,
        parent_loops: &Vec<(src::BlockId, usize)>,
        block_id: src::BlockId,
    ) -> Option<FilteredLoopParents> {
        let mut eliminate: usize = 0;
        for (i, (loop_id, _)) in parent_loops.iter().enumerate().rev() {
            if Self::loop_entry_is_reachable_from_inner(cfg, *loop_id, block_id) {
                eliminate = i + 1;
                break;
            }
        }

        // Split the vector of parents
        let (remaining_parents, removed_parents) = parent_loops.split_at(eliminate);
        if !removed_parents.is_empty() {
            let (mut remaining_parents, removed_parents) =
                (remaining_parents.to_vec(), removed_parents.to_vec());

            // Update the distance to the last loop - we just increment the distance
            // by 1, because from the point of view of the parent loop, we just exited
            // a block and go to the next sequence of instructions.
            if !remaining_parents.is_empty() {
                remaining_parents.last_mut().unwrap().1 += 1;
            }

            Some(FilteredLoopParents {
                remaining_parents,
                removed_parents,
            })
        } else {
            None
        }
    }

    /// Auxiliary helper
    ///
    /// Check if it is possible to reach the exit of an outer switch from `start_bid` without going
    /// through the `exit_candidate`. We use the forward graph.
    fn can_reach_outer_exit(
        cfg: &CfgInfo,
        outer_exits: &HashSet<src::BlockId>,
        start_bid: src::BlockId,
        exit_candidate: src::BlockId,
    ) -> bool {
        /// Graph that is identical to `Cfg` except that a chosen node is considered to have no neighbors.
        struct GraphWithoutEdgesFrom<'a> {
            graph: &'a Cfg,
            special_node: BlockId,
        }
        impl GraphBase for GraphWithoutEdgesFrom<'_> {
            type EdgeId = <Cfg as GraphBase>::EdgeId;
            type NodeId = <Cfg as GraphBase>::NodeId;
        }
        impl IntoNeighbors for &GraphWithoutEdgesFrom<'_> {
            type Neighbors = impl Iterator<Item = Self::NodeId>;
            fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {
                if a == self.special_node {
                    None
                } else {
                    Some(self.graph.neighbors(a))
                }
                .into_iter()
                .flatten()
            }
        }
        impl Visitable for GraphWithoutEdgesFrom<'_> {
            type Map = <Cfg as Visitable>::Map;
            fn visit_map(self: &Self) -> Self::Map {
                self.graph.visit_map()
            }
            fn reset_map(self: &Self, map: &mut Self::Map) {
                self.graph.reset_map(map);
            }
        }

        // Do a DFS over the forward graph where we pretend that the exit candidate has no outgoing
        // edges. If we reach an outer exit candidate in that graph then the exit candidate does not
        // dominate the outer exit candidates in the forward graph starting from `start_bid`.
        let graph = GraphWithoutEdgesFrom {
            graph: &cfg.fwd_cfg,
            special_node: exit_candidate,
        };
        Dfs::new(&graph, start_bid)
            .iter(&graph)
            .any(|bid| outer_exits.contains(&bid))
    }
    /// Register a node and its children as exit candidates for a list of
    /// parent loops.
    fn register_children_as_loop_exit_candidates(
        cfg: &CfgInfo,
        loop_exits: &mut HashMap<src::BlockId, IndexMap<src::BlockId, LoopExitCandidateInfo>>,
        removed_parent_loops: &Vec<(src::BlockId, usize)>,
        block_id: src::BlockId,
    ) {
        let mut base_dist = 0;
        // For every parent loop, in reverse order (we go from last to first in
        // order to correctly compute the distances)
        for (loop_id, loop_dist) in removed_parent_loops.iter().rev() {
            // Update the distance to the loop entry
            base_dist += *loop_dist;

            // Retrieve the candidates
            let candidates = loop_exits.get_mut(loop_id).unwrap();

            // Update them
            for (bid, dist) in cfg.block_data(block_id).shortest_paths_including_self() {
                let distance = base_dist + dist;
                match candidates.get_mut(&bid) {
                    None => {
                        candidates.insert(
                            bid,
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

    /// Compute the loop exit candidates.
    ///
    /// There may be several candidates with the same "optimality" (same number of
    /// occurrences, etc.), in which case we choose the first one which was registered
    /// (the order in which we explore the graph is deterministic): this is why we
    /// store the candidates in a linked hash map.
    fn compute_loop_exit_candidates(
        cfg: &CfgInfo,
        explored: &mut HashSet<src::BlockId>,
        ordered_loops: &mut Vec<src::BlockId>,
        loop_exits: &mut HashMap<src::BlockId, IndexMap<src::BlockId, LoopExitCandidateInfo>>,
        // List of parent loops, with the distance to the entry of the loop (the distance
        // is the distance between the current node and the loop entry for the last parent,
        // and the distance between the parents for the others).
        mut parent_loops: Vec<(src::BlockId, usize)>,
        block_id: src::BlockId,
    ) {
        if explored.contains(&block_id) {
            return;
        }
        explored.insert(block_id);

        // Check if we enter a loop - add the corresponding node if necessary
        if cfg.loop_entries.contains(&block_id) {
            parent_loops.push((block_id, 1));
            ordered_loops.push(block_id);
        } else {
            // Increase the distance with the parent loop
            if !parent_loops.is_empty() {
                parent_loops.last_mut().unwrap().1 += 1;
            }
        };

        // Retrieve the children - note that we ignore the back edges
        for child in cfg.fwd_cfg.neighbors(block_id) {
            // If the parent loop entry is not reachable from the child without going
            // through a backward edge which goes directly to the loop entry, consider
            // this node a potential exit.
            ensure_sufficient_stack(|| {
                let new_parent_loops = match Self::filter_loop_parents(cfg, &parent_loops, child) {
                    None => parent_loops.clone(),
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
                        Self::register_children_as_loop_exit_candidates(
                            cfg,
                            loop_exits,
                            &fparent_loops.removed_parents,
                            child,
                        );
                        fparent_loops.remaining_parents
                    }
                };
                // Explore, with the filtered parents
                Self::compute_loop_exit_candidates(
                    cfg,
                    explored,
                    ordered_loops,
                    loop_exits,
                    new_parent_loops,
                    child,
                );
            })
        }
    }

    /// See [`compute_loop_switch_exits`] for
    /// explanations about what "exits" are.
    ///
    /// The following function computes the loop exits. It acts as follows.
    ///
    /// We keep track of a stack of the loops in which we entered.
    /// It is very easy to check when we enter a loop: loop entries are destinations
    /// of backward edges, which can be spotted with a simple graph exploration (see
    /// [`build_cfg_partial_info_edges`].
    /// The criteria to consider whether we exit a loop is the following:
    /// - we exit a loop if we go to a block from which we can't reach the loop
    ///   entry at all
    /// - or if we can reach the loop entry, but must use a backward edge which goes
    ///   to an outer loop
    ///
    /// It is better explained on the following example:
    /// ```text
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
    /// ```text
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
    /// - it is the one which is used the most times (note that there can be
    ///   several candidates which are referenced strictly more than once: see the
    ///   comment below)
    /// - if several exits have the same number of occurrences, we choose the one
    ///   for which we goto the "earliest" (earliest meaning that the goto is close to
    ///   the loop entry node in the AST). The reason is that all the loops should
    ///   have an outer if ... then ... else ... which executes the loop body or goes
    ///   to the exit (note that this is not necessarily the first
    ///   if ... then ... else ... we find: loop conditions can be arbitrary
    ///   expressions, containing branchings).
    ///
    /// # Several candidates for a loop exit:
    /// =====================================
    /// There used to be a sanity check to ensure there are no two different
    /// candidates with exactly the same number of occurrences and distance from
    /// the entry of the loop, if the number of occurrences is > 1.
    ///
    /// We removed it because it does happen, for instance here (the match
    /// introduces an `unreachable` node, and it has the same number of
    /// occurrences and the same distance to the loop entry as the `panic`
    /// node):
    ///
    /// ```text
    /// pub fn list_nth_mut_loop_pair<'a, T>(
    ///     mut ls: &'a mut List<T>,
    ///     mut i: u32,
    /// ) -> &'a mut T {
    ///     loop {
    ///         match ls {
    ///             List::Nil => {
    ///                 panic!() // <-- best candidate
    ///             }
    ///             List::Cons(x, tl) => {
    ///                 if i == 0 {
    ///                     return x;
    ///                 } else {
    ///                     ls = tl;
    ///                     i -= 1;
    ///                 }
    ///             }
    ///             _ => {
    ///               // Note that Rustc always introduces an unreachable branch after
    ///               // desugaring matches.
    ///               unreachable!(), // <-- best candidate
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// When this happens we choose an exit candidate whose edges don't necessarily
    /// lead to an error (above there are none, so we don't choose any exits). Note
    /// that this last condition is important to prevent loops from being unnecessarily
    /// nested:
    ///
    /// ```text
    /// pub fn nested_loops_enum(step_out: usize, step_in: usize) -> usize {
    ///     let mut s = 0;
    ///
    ///     for _ in 0..128 { // We don't want this loop to be nested with the loops below
    ///         s += 1;
    ///     }
    ///
    ///     for _ in 0..(step_out) {
    ///         for _ in 0..(step_in) {
    ///             s += 1;
    ///         }
    ///     }
    ///
    ///     s
    /// }
    /// ```
    fn compute_loop_exits(
        ctx: &mut TransformCtx,
        body: &src::ExprBody,
        cfg: &CfgInfo,
    ) -> HashMap<src::BlockId, Option<src::BlockId>> {
        let mut explored = HashSet::new();
        let mut ordered_loops = Vec::new();
        let mut loop_exits = HashMap::new();

        // Initialize the loop exits candidates
        for loop_id in &cfg.loop_entries {
            loop_exits.insert(*loop_id, IndexMap::new());
        }

        // Compute the candidates
        Self::compute_loop_exit_candidates(
            cfg,
            &mut explored,
            &mut ordered_loops,
            &mut loop_exits,
            Vec::new(),
            src::BlockId::ZERO,
        );

        {
            // Debugging
            let candidates: Vec<String> = loop_exits
                .iter()
                .map(|(loop_id, candidates)| format!("{loop_id} -> {candidates:?}"))
                .collect();
            trace!("Loop exit candidates:\n{}", candidates.join("\n"));
        }

        // Choose one candidate among the potential candidates.
        let mut exits: HashSet<src::BlockId> = HashSet::new();
        let mut chosen_loop_exits: HashMap<src::BlockId, Option<src::BlockId>> = HashMap::new();
        // For every loop
        for loop_id in ordered_loops {
            // Check the candidates.
            // Ignore the candidates which have already been chosen as exits for other
            // loops (which should be outer loops).
            // We choose the exit with:
            // - the most occurrences
            // - the least total distance (if there are several possibilities)
            // - doesn't necessarily lead to an error (panic, unreachable)

            // First:
            // - filter the candidates
            // - compute the number of occurrences
            // - compute the sum of distances
            // TODO: we could simply order by using a lexicographic order
            let loop_exits = loop_exits
                .get(&loop_id)
                .unwrap()
                .iter()
                // If candidate already selected for another loop: ignore
                .filter(|(candidate_id, _)| !exits.contains(candidate_id))
                .map(|(candidate_id, candidate_info)| {
                    let num_occurrences = candidate_info.occurrences.len();
                    let dist_sum = candidate_info.occurrences.iter().sum();
                    (*candidate_id, num_occurrences, dist_sum)
                })
                .collect_vec();

            trace!(
                "Loop {}: possible exits:\n{}",
                loop_id,
                loop_exits
                    .iter()
                    .map(|(bid, occs, dsum)| format!(
                        "{bid} -> {{ occurrences: {occs}, dist_sum: {dsum} }}",
                    ))
                    .collect::<Vec<String>>()
                    .join("\n")
            );

            // Second: actually select the proper candidate.

            // We find the one with the highest occurrence and the smallest distance
            // from the entry of the loop (note that we take care of listing the exit
            // candidates in a deterministic order).
            let mut best_exit: Option<src::BlockId> = None;
            let mut best_occurrences = 0;
            let mut best_dist_sum = std::usize::MAX;
            for (candidate_id, occurrences, dist_sum) in &loop_exits {
                if (*occurrences > best_occurrences)
                    || (*occurrences == best_occurrences && *dist_sum < best_dist_sum)
                {
                    best_exit = Some(*candidate_id);
                    best_occurrences = *occurrences;
                    best_dist_sum = *dist_sum;
                }
            }

            let possible_candidates: Vec<_> = loop_exits
                .iter()
                .filter_map(|(bid, occs, dsum)| {
                    if *occs == best_occurrences && *dsum == best_dist_sum {
                        Some(*bid)
                    } else {
                        None
                    }
                })
                .collect();
            let num_possible_candidates = loop_exits.len();

            // If there is exactly one one best candidate, it is easy.
            // Otherwise we need to split further.
            if num_possible_candidates > 1 {
                trace!("Best candidates: {:?}", possible_candidates);
                // TODO: if we use a lexicographic order we can merge this with the code
                // above.
                // Remove the candidates which only lead to errors (panic or unreachable).
                let candidates: Vec<_> = possible_candidates
                    .iter()
                    .filter(|&&bid| !cfg.block_data[bid].only_reach_error)
                    .collect();
                // If there is exactly one candidate we select it
                if candidates.len() == 1 {
                    let exit_id = *candidates[0];
                    exits.insert(exit_id);
                    trace!("Loop {loop_id}: selected the best exit candidate {exit_id}");
                    chosen_loop_exits.insert(loop_id, Some(exit_id));
                } else {
                    // Otherwise we do not select any exit.
                    // We don't want to select any exit if we are in the below situation
                    // (all paths lead to errors). We added a sanity check below to
                    // catch the situations where there are several exits which don't
                    // lead to errors.
                    //
                    // Example:
                    // ========
                    // ```
                    // loop {
                    //     match ls {
                    //         List::Nil => {
                    //             panic!() // <-- best candidate
                    //         }
                    //         List::Cons(x, tl) => {
                    //             if i == 0 {
                    //                 return x;
                    //             } else {
                    //                 ls = tl;
                    //                 i -= 1;
                    //             }
                    //         }
                    //         _ => {
                    //           unreachable!(); // <-- best candidate (Rustc introduces an `unreachable` case)
                    //         }
                    //     }
                    // }
                    // ```
                    //
                    // Adding this sanity check so that we can see when there are
                    // several candidates.
                    let span = body.body[loop_id].terminator.span; // Taking *a* span from the block
                    sanity_check!(ctx, span, candidates.is_empty());
                    trace!(
                        "Loop {loop_id}: did not select an exit candidate because they all lead to panics"
                    );
                    chosen_loop_exits.insert(loop_id, None);
                }
            } else {
                // Register the exit, if there is one
                if let Some(exit_id) = best_exit {
                    exits.insert(exit_id);
                }
                chosen_loop_exits.insert(loop_id, best_exit);
            }
        }

        // Return the chosen exits
        trace!("Chosen loop exits: {:?}", chosen_loop_exits);
        chosen_loop_exits
    }

    /// See [`compute_loop_switch_exits`] for
    /// explanations about what "exits" are.
    ///
    /// In order to compute the switch exits, we simply recursively compute a
    /// topologically ordered set of "filtered successors" as follows (note
    /// that we work in the CFG *without* back edges):
    /// - for a block which doesn't branch (only one successor), the filtered
    ///   successors is the set of reachable nodes.
    /// - for a block which branches, we compute the nodes reachable from all
    ///   the children, and find the "best" intersection between those.
    ///   Note that we find the "best" intersection (a pair of branches which
    ///   maximize the intersection of filtered successors) because some branches
    ///   might never join the control-flow of the other branches, if they contain
    ///   a `break`, `return`, `panic`, etc., like here:
    ///   ```text
    ///   if b { x = 3; } { return; }
    ///   y += x;
    ///   ...
    ///   ```
    /// Note that with nested switches, the branches of the inner switches might
    /// goto the exits of the outer switches: for this reason, we give precedence
    /// to the outer switches.
    fn compute_switch_exits(cfg: &CfgInfo) -> HashMap<src::BlockId, Option<src::BlockId>> {
        // Compute the successors info map, starting at the root node
        trace!(
            "- cfg.cfg:\n{:?}\n- cfg.cfg_no_be:\n{:?}\n- cfg.switch_blocks:\n{:?}",
            cfg.cfg, cfg.fwd_cfg, cfg.switch_blocks
        );

        // We need to give precedence to the outer switches: we thus iterate
        // over the switch blocks in topological order.
        let mut sorted_switch_blocks: BTreeSet<OrdBlockId> = BTreeSet::new();
        for bid in cfg.switch_blocks.iter() {
            sorted_switch_blocks.insert(cfg.make_ord_block_id(*bid));
        }
        trace!("sorted_switch_blocks: {:?}", sorted_switch_blocks);

        // Debugging: print all the successors
        {
            trace!("Successors info:\n{}\n", {
                let mut out = vec![];
                for (bid, info) in cfg.block_data.iter_indexed() {
                    out.push(format!("{} -> {{flow: {:?}}}", bid, &info.flow).to_string());
                }
                out.join("\n")
            });
        }

        // For every node which is a switch, retrieve the exit.
        // As the set of intersection of successors is topologically sorted, the
        // exit should be the first node in the set (if the set is non empty).
        // Also, we need to explore the nodes in topological order, to give
        // precedence to the outer switches.
        let mut exits_set = HashSet::new();
        let mut exits = HashMap::new();
        for bid in sorted_switch_blocks {
            trace!("Finding exit candidate for: {bid:?}");
            let bid = bid.id;
            let block_data = &cfg.block_data[bid];
            // Find the best successor: this is the node with the highest flow, and the
            // highest reverse topological rank.
            //
            // Remark: in order to rank the nodes, we also use the negation of the
            // rank given by the topological order. The last elements of the set
            // have the highest flow, that is they are the nodes to which the maximum
            // number of paths converge. If several nodes have the same flow, we want
            // to take the highest one in the hierarchy: hence the use of the inverse
            // of the topological rank.
            //
            // Ex.:
            // ```text
            // A  -- we start here
            // |
            // |---------------------------------------
            // |            |            |            |
            // B:(0.25,-1)  C:(0.25,-2)  D:(0.25,-3)  E:(0.25,-4)
            // |            |            |
            // |--------------------------
            // |
            // F:(0.75,-5)
            // |
            // |
            // G:(0.75,-6)
            // ```
            // The "best" node (with the highest (flow, rank) in the graph above is F.
            let switch_exit: Option<BlockWithRank<(BigRational, isize)>> = block_data
                .reachable_excluding_self()
                .map(|id| {
                    let flow = block_data.flow[id].clone();
                    let rank = -isize::try_from(cfg.topo_rank(id)).unwrap();
                    BlockWithRank {
                        rank: (flow, rank),
                        id,
                    }
                })
                .max();
            let exit = if let Some(exit) = switch_exit {
                // We have an exit candidate: check that it was not already
                // taken by an external switch
                trace!("{bid:?} has an exit candidate: {exit:?}");
                if exits_set.contains(&exit.id) {
                    trace!(
                        "Ignoring the exit candidate because already taken by an external switch"
                    );
                    None
                } else {
                    // It was not taken by an external switch.
                    //
                    // We must check that we can't reach the exit of an external
                    // switch from one of the branches, without going through the
                    // exit candidate.
                    // We do this by simply checking that we can't reach any exits
                    // (and use the fact that we explore the switch by using a
                    // topological order to not discard valid exit candidates).
                    //
                    // The reason is that it can lead to code like the following:
                    // ```
                    // if ... { // if #1
                    //   if ... { // if #2
                    //     ...
                    //     // here, we have a `goto b1`, where b1 is the exit
                    //     // of if #2: we thus stop translating the blocks.
                    //   }
                    //   else {
                    //     ...
                    //     // here, we have a `goto b2`, where b2 is the exit
                    //     // of if #1: we thus stop translating the blocks.
                    //   }
                    //   // We insert code for the block b1 here (which is the exit of
                    //   // the exit of if #2). However, this block should only
                    //   // be executed in the branch "then" of the if #2, not in
                    //   // the branch "else".
                    //   ...
                    // }
                    // else {
                    //   ...
                    // }
                    // ```

                    // First: we do a quick check (does the set of all successors
                    // intersect the set of exits for outer blocks?). If yes, we do
                    // a more precise analysis: we check if we can reach the exit
                    // *without going through* the exit candidate.
                    let can_reach_exit = block_data
                        .reachable_excluding_self()
                        .any(|bid| exits_set.contains(&bid));
                    if !can_reach_exit || !Self::can_reach_outer_exit(cfg, &exits_set, bid, exit.id)
                    {
                        trace!("Keeping the exit candidate");
                        // No intersection: ok
                        exits_set.insert(exit.id);
                        Some(exit.id)
                    } else {
                        trace!(
                            "Ignoring the exit candidate because of an intersection with external switches"
                        );
                        None
                    }
                }
            } else {
                trace!("{bid:?} has no successors");
                None
            };

            exits.insert(bid, exit);
        }

        exits
    }

    /// Compute the exits for the loops and the switches (switch on integer and
    /// if ... then ... else ...). We need to do this because control-flow in MIR
    /// is destructured: we have gotos everywhere.
    ///
    /// Let's consider the following piece of code:
    /// ```text
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
    /// ```text
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
    /// ```text
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
    /// ```text
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
    /// ```text
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
    fn compute(ctx: &mut TransformCtx, body: &src::ExprBody, cfg_info: &CfgInfo) -> Self {
        // Compute the loop exits
        let loop_exits = Self::compute_loop_exits(ctx, body, cfg_info);
        trace!("loop_exits:\n{:?}", loop_exits);

        // Compute the switch exits
        let switch_exits = Self::compute_switch_exits(cfg_info);
        trace!("switch_exits:\n{:?}", switch_exits);

        // Compute the exit info
        let mut exits_info = ExitsInfo {
            exits: body.body.map_ref(|_| Default::default()),
        };

        // We need to give precedence to the outer switches and loops: we thus iterate
        // over the blocks in topological order.
        let mut sorted_blocks: BTreeSet<OrdBlockId> = BTreeSet::new();
        for bid in cfg_info
            .loop_entries
            .iter()
            .chain(cfg_info.switch_blocks.iter())
        {
            sorted_blocks.insert(cfg_info.make_ord_block_id(*bid));
        }

        // Keep track of the exits which were already attributed
        let mut all_exits = HashSet::new();

        // Put all this together
        for bid in sorted_blocks {
            let bid = bid.id;
            // Check if loop or switch block
            let exit_info = &mut exits_info.exits[bid];
            if cfg_info.loop_entries.contains(&bid) {
                exit_info.is_loop_entry = true;
                // This is a loop.
                //
                // For loops, we always register the exit (if there is one).
                // However, the exit may be owned by an outer switch (note
                // that we already took care of spreading the exits between
                // the inner/outer loops)
                let exit_id = loop_exits.get(&bid).unwrap();
                exit_info.loop_exit = *exit_id;
                // Check if we "own" the exit
                let exit_id = exit_id.filter(|exit_id| !all_exits.contains(exit_id));
                if let Some(exit_id) = exit_id {
                    all_exits.insert(exit_id);
                }
                exit_info.owned_loop_exit = exit_id;
            } else {
                exit_info.is_switch_entry = true;
                // For switches: check that the exit was not already given to a
                // loop
                let exit_id = switch_exits.get(&bid).unwrap();
                // Check if we "own" the exit
                let exit_id = exit_id.filter(|exit_id| !all_exits.contains(exit_id));
                if let Some(exit_id) = exit_id {
                    all_exits.insert(exit_id);
                }
                exit_info.owned_switch_exit = exit_id;
            }
        }

        exits_info
    }
}

enum GotoKind {
    Break(usize),
    Continue(usize),
    ExitBlock,
    Goto,
}

struct ReconstructCtx<'a> {
    body: &'a src::ExprBody,
    exits_info: ExitsInfo,
    explored: HashSet<src::BlockId>,
    parent_loops: Vec<src::BlockId>,
    switch_exit_blocks: HashSet<src::BlockId>,
}

impl<'a> ReconstructCtx<'a> {
    fn build(ctx: &mut TransformCtx, src_body: &'a src::ExprBody) -> Result<Self, Irreducible> {
        // Explore the function body to create the control-flow graph without backward
        // edges, and identify the loop entries (which are destinations of backward edges).
        let cfg_info = CfgInfo::build(&src_body.body)?;

        // Find the exit block for all the loops and switches, if such an exit point exists.
        let exits_info = ExitsInfo::compute(ctx, src_body, &cfg_info);

        // Translate the body by reconstructing the loops and the
        // conditional branchings.
        // Note that we shouldn't get `None`.
        Ok(ReconstructCtx {
            body: src_body,
            exits_info: exits_info,
            explored: HashSet::new(),
            parent_loops: Vec::new(),
            switch_exit_blocks: HashSet::new(),
        })
    }

    fn get_goto_kind(&self, next_block_id: src::BlockId) -> GotoKind {
        // First explore the parent loops in revert order
        for (i, &loop_id) in self.parent_loops.iter().rev().enumerate() {
            // If we goto a loop entry node: this is a 'continue'
            if next_block_id == loop_id {
                return GotoKind::Continue(i);
            } else {
                // If we goto a loop exit node: this is a 'break'
                if let Some(exit_id) = self.exits_info.exits[loop_id].loop_exit {
                    if next_block_id == exit_id {
                        return GotoKind::Break(i);
                    }
                }
            }
        }

        // Check if the goto exits the current block
        if self.switch_exit_blocks.contains(&next_block_id) {
            return GotoKind::ExitBlock;
        }

        // Default
        GotoKind::Goto
    }

    /// `parent_span`: we need some span data for the new statement.
    /// We use the one for the parent terminator.
    fn translate_child_block(&mut self, parent_span: Span, child_id: src::BlockId) -> tgt::Block {
        // Check if this is a backward call
        match self.get_goto_kind(child_id) {
            GotoKind::Break(index) => {
                let st = tgt::StatementKind::Break(index);
                tgt::Statement::new(parent_span, st).into_block()
            }
            GotoKind::Continue(index) => {
                let st = tgt::StatementKind::Continue(index);
                tgt::Statement::new(parent_span, st).into_block()
            }
            // If we are going to an exit block we simply ignore the goto
            GotoKind::ExitBlock => {
                let st = tgt::StatementKind::Nop;
                tgt::Statement::new(parent_span, st).into_block()
            }
            GotoKind::Goto => {
                // "Standard" goto: just recursively translate
                ensure_sufficient_stack(|| self.translate_block(child_id))
            }
        }
    }

    fn translate_statement(&self, st: &src::Statement) -> Option<tgt::Statement> {
        let src_span = st.span;
        let st = match st.kind.clone() {
            src::StatementKind::Assign(place, rvalue) => tgt::StatementKind::Assign(place, rvalue),
            src::StatementKind::SetDiscriminant(place, variant_id) => {
                tgt::StatementKind::SetDiscriminant(place, variant_id)
            }
            src::StatementKind::CopyNonOverlapping(copy) => {
                tgt::StatementKind::CopyNonOverlapping(copy)
            }
            src::StatementKind::StorageLive(var_id) => tgt::StatementKind::StorageLive(var_id),
            src::StatementKind::StorageDead(var_id) => tgt::StatementKind::StorageDead(var_id),
            src::StatementKind::Deinit(place) => tgt::StatementKind::Deinit(place),
            src::StatementKind::Assert(assert) => tgt::StatementKind::Assert(assert),
            src::StatementKind::Nop => tgt::StatementKind::Nop,
            src::StatementKind::Error(s) => tgt::StatementKind::Error(s),
        };
        Some(tgt::Statement::new(src_span, st))
    }

    fn translate_terminator(&mut self, terminator: &src::Terminator) -> tgt::Block {
        let src_span = terminator.span;

        match &terminator.kind {
            src::TerminatorKind::Abort(kind) => {
                tgt::Statement::new(src_span, tgt::StatementKind::Abort(kind.clone())).into_block()
            }
            src::TerminatorKind::Return => {
                tgt::Statement::new(src_span, tgt::StatementKind::Return).into_block()
            }
            src::TerminatorKind::UnwindResume => {
                tgt::Statement::new(src_span, tgt::StatementKind::Abort(AbortKind::Panic(None)))
                    .into_block()
            }
            src::TerminatorKind::Call {
                call,
                target,
                on_unwind: _,
            } => {
                // TODO: Have unwinds in the LLBC
                let st = tgt::Statement::new(src_span, tgt::StatementKind::Call(call.clone()));
                let mut block = self.translate_child_block(terminator.span, *target);
                block.statements.insert(0, st);
                block
            }
            src::TerminatorKind::Drop {
                kind,
                place,
                tref,
                target,
                on_unwind: _,
            } => {
                // TODO: Have unwinds in the LLBC
                let st = tgt::Statement::new(
                    src_span,
                    tgt::StatementKind::Drop(place.clone(), tref.clone(), kind.clone()),
                );
                let mut block = self.translate_child_block(terminator.span, *target);
                block.statements.insert(0, st);
                block
            }
            src::TerminatorKind::Goto { target } => {
                self.translate_child_block(terminator.span, *target)
            }
            src::TerminatorKind::Switch { discr, targets } => {
                // Translate the target expressions
                let switch = match &targets {
                    src::SwitchTargets::If(then_tgt, else_tgt) => {
                        let then_block = self.translate_child_block(terminator.span, *then_tgt);
                        let else_block = self.translate_child_block(terminator.span, *else_tgt);
                        tgt::Switch::If(discr.clone(), then_block, else_block)
                    }
                    src::SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                        // Note that some branches can be grouped together, like
                        // here:
                        // ```
                        // match e {
                        //   E::V1 | E::V2 => ..., // Grouped
                        //   E::V3 => ...
                        // }
                        // ```
                        // We detect this by checking if a block has already been
                        // translated as one of the branches of the switch.
                        //
                        // Rk.: note there may be intermediate gotos depending
                        // on the MIR we use. Typically, we manage to detect the
                        // grouped branches with Optimized MIR, but not with Promoted
                        // MIR. See the comment in "tests/src/matches.rs".

                        // We link block ids to:
                        // - vector of matched integer values
                        // - translated blocks
                        let mut branches: IndexMap<src::BlockId, (Vec<Literal>, tgt::Block)> =
                            IndexMap::new();

                        // Translate the children expressions
                        for (v, bid) in targets.iter() {
                            // Check if the block has already been translated:
                            // if yes, it means we need to group branches
                            if branches.contains_key(bid) {
                                // Already translated: add the matched value to
                                // the list of values
                                let branch = branches.get_mut(bid).unwrap();
                                branch.0.push(v.clone());
                            } else {
                                // Not translated: translate it
                                let block = self.translate_child_block(terminator.span, *bid);
                                // We use the terminator span information in case then
                                // then statement is `None`
                                branches.insert(*bid, (vec![v.clone()], block));
                            }
                        }
                        let targets_blocks: Vec<(Vec<Literal>, tgt::Block)> =
                            branches.into_iter().map(|(_, x)| x).collect();

                        let otherwise_block =
                            self.translate_child_block(terminator.span, *otherwise);

                        // Translate
                        tgt::Switch::SwitchInt(
                            discr.clone(),
                            *int_ty,
                            targets_blocks,
                            otherwise_block,
                        )
                    }
                };

                // Return
                let span = tgt::combine_switch_targets_span(&switch);
                let span = combine_span(&src_span, &span);
                let st = tgt::StatementKind::Switch(switch);
                tgt::Statement::new(span, st).into_block()
            }
        }
    }

    /// Remark: some values are boxed (here, the returned statement) so that they
    /// are allocated on the heap. This reduces stack usage (we had problems with
    /// stack overflows in the past). A more efficient solution would be to use loops
    /// to make this code constant space, but that would require a serious rewriting.
    fn translate_block(&mut self, block_id: src::BlockId) -> tgt::Block {
        // If the user activated this check: check that we didn't already translate
        // this block, and insert the block id in the set of already translated blocks.
        self.explored.insert(block_id);

        let block = &self.body.body[block_id];

        let exit_info = &self.exits_info.exits[block_id];
        // Check if we enter a loop: if so, update parent_loops and the current_exit_block
        let is_loop = exit_info.is_loop_entry;
        // If we enter a switch or a loop, we need to check if we own the exit
        // block, in which case we need to append it to the loop/switch body
        // in a sequence
        let is_switch = exit_info.is_switch_entry;
        let next_block = if is_loop {
            exit_info.owned_loop_exit
        } else if is_switch {
            exit_info.owned_switch_exit
        } else {
            None
        };

        let terminator = {
            if is_loop {
                self.parent_loops.push(block_id);
            }
            // If we enter a switch, add the exit block to the set of outer exit blocks.
            if is_switch && let Some(bid) = next_block {
                assert!(!self.switch_exit_blocks.contains(&bid));
                self.switch_exit_blocks.insert(bid);
            }

            // Translate the terminator and the subsequent blocks.
            // Note that this terminator is an option: we might ignore it
            // (if it is an exit).
            let terminator = self.translate_terminator(&block.terminator);

            // Reset the state to what it was previously.
            if is_loop {
                self.parent_loops.pop();
            }
            if is_switch && let Some(bid) = next_block {
                self.switch_exit_blocks.remove(&bid);
            }
            terminator
        };

        // Translate the statements inside the block
        let statements = block
            .statements
            .iter()
            .filter_map(|st| self.translate_statement(st))
            .collect_vec();

        // Prepend the statements to the terminator.
        let mut block = if let Some(st) = tgt::Block::from_seq(statements) {
            st.merge(terminator)
        } else {
            terminator
        };

        if is_loop {
            // Put the loop body inside a `Loop`.
            block = tgt::Statement::new(block.span, tgt::StatementKind::Loop(block)).into_block()
        } else if !is_switch {
            assert!(next_block.is_none());
        }

        // Concatenate the exit expression, if needs be
        if let Some(exit_block_id) = next_block {
            let next_block = ensure_sufficient_stack(|| self.translate_block(exit_block_id));
            block = block.merge(next_block);
        }
        block
    }
}

fn translate_body(ctx: &mut TransformCtx, body: &mut gast::Body) {
    use gast::Body::{Structured, Unstructured};
    let Unstructured(src_body) = body else {
        panic!("Called `ullbc_to_llbc` on an already restructured body")
    };
    trace!("About to translate to ullbc: {:?}", src_body.span);

    // Calculate info about the graph and heuristically determine loop and switch exit blocks.
    let mut ctx = match ReconstructCtx::build(ctx, src_body) {
        Ok(ctx) => ctx,
        Err(Irreducible(bid)) => {
            let span = src_body.body[bid].terminator.span;
            register_error!(
                ctx,
                span,
                "the control-flow graph of this function is not reducible"
            );
            panic!("can't reconstruct irreducible control-flow")
        }
    };
    // Translate the blocks using the computed data.
    let tgt_body = ctx.translate_block(src::BlockId::ZERO);

    let tgt_body = tgt::ExprBody {
        span: src_body.span,
        locals: src_body.locals.clone(),
        bound_body_regions: src_body.bound_body_regions,
        body: tgt_body,
        comments: src_body.comments.clone(),
    };
    *body = Structured(tgt_body);
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Translate the bodies one at a time.
        ctx.for_each_body(|ctx, body| {
            translate_body(ctx, body);
        });

        // Print the functions
        let fmt_ctx = &ctx.into_fmt();
        for fun in &ctx.translated.fun_decls {
            trace!(
                "# Signature:\n{}\n\n# Function definition:\n{}\n",
                fun.signature.with_ctx(fmt_ctx),
                fun.with_ctx(fmt_ctx),
            );
        }

        if ctx.options.print_built_llbc {
            eprintln!("# LLBC resulting from control-flow reconstruction:\n\n{ctx}\n",);
        }
    }
}
