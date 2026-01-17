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
use itertools::Itertools;
use petgraph::algo::dijkstra;
use petgraph::algo::dominators::{Dominators, simple_fast};
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::{
    Dfs, DfsPostOrder, EdgeFiltered, EdgeRef, GraphRef, IntoNeighbors, VisitMap, Visitable, Walker,
};
use smallvec::SmallVec;
use std::cmp::Reverse;
use std::collections::HashSet;
use std::mem;

use crate::common::ensure_sufficient_stack;
use crate::errors::sanity_check;
use crate::ids::IndexVec;
use crate::llbc_ast as tgt;
use crate::meta::{Span, combine_span};
use crate::transform::TransformCtx;
use crate::transform::ctx::TransformPass;
use crate::ullbc_ast::{self as src, BlockId};
use crate::{ast::*, register_error};

pub enum StackAction<N> {
    PopPath,
    Explore(N),
}
pub struct DfsWithPath<N, VM> {
    /// The stack of nodes to visit
    pub stack: Vec<StackAction<N>>,
    /// The map of discovered nodes
    pub discovered: VM,
    /// The path from start node to current node.
    pub path: Vec<N>,
}
impl<N, VM> DfsWithPath<N, VM>
where
    N: Copy + PartialEq,
    VM: VisitMap<N>,
{
    /// Create a new **DfsWithPath**, using the graph's visitor map, and put **start** in the stack
    /// of nodes to visit.
    pub fn new<G>(graph: G, start: N) -> Self
    where
        G: GraphRef + Visitable<NodeId = N, Map = VM>,
    {
        Self {
            stack: vec![StackAction::Explore(start)],
            discovered: graph.visit_map(),
            path: vec![],
        }
    }

    /// Return the next node in the dfs, or **None** if the traversal is done.
    pub fn next<G>(&mut self, graph: G) -> Option<N>
    where
        G: IntoNeighbors<NodeId = N>,
    {
        while let Some(action) = self.stack.pop() {
            match action {
                StackAction::Explore(node) => {
                    if self.discovered.visit(node) {
                        self.path.push(node);
                        self.stack.push(StackAction::PopPath);
                        for succ in graph.neighbors(node) {
                            if !self.discovered.is_visited(&succ) {
                                self.stack.push(StackAction::Explore(succ));
                            }
                        }
                        return Some(node);
                    }
                }
                StackAction::PopPath => {
                    self.path.pop();
                }
            }
        }
        None
    }
}

/// Arbitrary-precision numbers
type BigUint = fraction::DynaInt<u64, fraction::BigUint>;
type BigRational = fraction::Ratio<BigUint>;

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId, ()>;

/// Information precomputed about a function's CFG.
#[derive(Debug)]
struct CfgInfo<'a> {
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
    pub block_data: IndexVec<BlockId, BlockData<'a>>,
}

#[derive(Debug)]
struct BlockData<'a> {
    pub id: BlockId,
    pub contents: &'a src::BlockData,
    /// The (unique) entrypoints of each loop. Unique because we error on irreducible cfgs.
    pub is_loop_header: bool,
    /// Whether this block is a switch.
    pub is_switch: bool,
    /// Blocks that have multiple incoming control-flow edges.
    pub is_merge_target: bool,
    /// Order in a reverse postorder numbering. `None` if the block is unreachable.
    pub reverse_postorder: Option<u32>,
    /// Nodes that this block immediately dominates. Sorted by reverse_postorder_id, with largest
    /// id first.
    pub immediately_dominates: SmallVec<[BlockId; 2]>,
    /// List of loops inside of which this node is (loops are identified by their header). A node
    /// is considered inside a loop if it is reachable from the loop header and if it can reach the
    /// loop header using only the backwards edges into it (i.e. we don't count a path that enters
    /// the loop header through a forward edge).
    ///
    /// Note that we might have to take a backward edge to reach the loop header, e.g.:
    ///   'a: loop {
    ///       // ...
    ///       'b: loop {
    ///           // ...
    ///           if true {
    ///               continue 'a;
    ///           } else {
    ///               if true {
    ///                   break 'a;
    ///               }
    ///               // This node has to take two backward edges in order to reach the start of `'a`.
    ///           }
    ///       }
    ///   }
    ///
    /// The restriction on backwards edges is for the following case:
    ///   loop {
    ///     loop {
    ///       ..
    ///     }
    ///     // Not in inner loop
    ///   }
    ///
    /// This is sorted by path order from the graph root.
    pub within_loops: SmallVec<[BlockId; 2]>,
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
    /// Reconstructed information about loops and switches.
    pub exit_info: ExitInfo,
}

#[derive(Debug, Default, Clone)]
struct ExitInfo {
    /// The loop exit
    loop_exit: Option<src::BlockId>,
    /// The switch exit.
    switch_exit: Option<src::BlockId>,
}

/// Error indicating that the control-flow graph is not reducible. The contained block id is a
/// block involved in an irreducible subgraph.
struct Irreducible(BlockId);

impl<'a> CfgInfo<'a> {
    /// Build the CFGs (the "regular" CFG and the CFG without backward edges) and precompute a
    /// bunch of graph information about the CFG.
    fn build(ctx: &TransformCtx, body: &'a src::BodyContents) -> Result<Self, Irreducible> {
        // The steps in this function follow a precise order, as each step typically requires the
        // previous one.
        let start_block = BlockId::ZERO;

        let empty_flow = body.map_ref(|_| BigRational::new(0u64.into(), 1u64.into()));
        let mut block_data: IndexVec<BlockId, BlockData> =
            body.map_ref_indexed(|id, contents| BlockData {
                id,
                contents,
                is_loop_header: false,
                is_switch: false,
                is_merge_target: false,
                reverse_postorder: None,
                immediately_dominates: Default::default(),
                within_loops: Default::default(),
                only_reach_error: false,
                shortest_paths: Default::default(),
                flow: empty_flow.clone(),
                exit_info: Default::default(),
            });

        // Build the node graph (we ignore unwind paths for now).
        let mut cfg = Cfg::new();
        for (block_id, block) in body.iter_indexed() {
            cfg.add_node(block_id);
            for tgt in block.targets_ignoring_unwind() {
                cfg.add_edge(block_id, tgt, ());
            }
        }

        // Compute the dominator tree.
        let dominator_tree = simple_fast(&cfg, start_block);

        // Compute reverse postorder numbering.
        for (i, block_id) in DfsPostOrder::new(&cfg, start_block).iter(&cfg).enumerate() {
            let rev_post_id = body.len() - i;
            block_data[block_id].reverse_postorder = Some(rev_post_id.try_into().unwrap());

            // Store the dominator tree in `block_data`.
            if let Some(dominator) = dominator_tree.immediate_dominator(block_id) {
                block_data[dominator].immediately_dominates.push(block_id);
            }

            // Detect merge targets.
            if cfg
                .neighbors_directed(block_id, petgraph::Direction::Incoming)
                .count()
                >= 2
            {
                block_data[block_id].is_merge_target = true;
            }
        }

        // Compute the forward graph (without backward edges). We do a dfs while keeping track of
        // the path from the start node.
        let mut fwd_cfg = Cfg::new();
        let mut loop_entries = HashSet::new();
        let mut switch_blocks = HashSet::new();
        for block_id in Dfs::new(&cfg, start_block).iter(&cfg) {
            fwd_cfg.add_node(block_id);

            if body[block_id].terminator.kind.is_switch() {
                switch_blocks.insert(block_id);
                block_data[block_id].is_switch = true;
            }

            // Iterate over edges into this node (so that we can determine whether this node is a
            // loop header).
            for from in cfg.neighbors_directed(block_id, petgraph::Direction::Incoming) {
                // Check if the edge is a backward edge.
                if block_data[from].reverse_postorder >= block_data[block_id].reverse_postorder {
                    // This is a backward edge
                    block_data[block_id].is_loop_header = true;
                    loop_entries.insert(block_id);
                    // A cfg is reducible iff the target of every back edge dominates the
                    // edge's source.
                    if !dominator_tree.dominators(from).unwrap().contains(&block_id) {
                        return Err(Irreducible(from));
                    }
                } else {
                    fwd_cfg.add_edge(from, block_id, ());
                }
            }
        }

        // Finish filling in information.
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
            // The flow to self is 1.
            flow[block_id] = BigRational::new(1u64.into(), 1u64.into());
            // Divide the flow from each child to a given target block by the number of children.
            // This is a sparse matrix multiplication and could be implemented using a linalg
            // library.
            let num_children: BigUint = fwd_targets.len().into();
            for &child in &fwd_targets {
                for grandchild in block_data[child].reachable_including_self() {
                    // Flow from `child` to `grandchild`
                    flow[grandchild] += &block_data[child].flow[grandchild] / &num_children;
                }
            }
            block_data[block_id].flow = flow;

            // Compute shortest paths to all reachable nodes in the forward graph.
            block_data[block_id].shortest_paths = dijkstra(&fwd_cfg, block_id, None, |_| 1usize);

            // Fill in the rest of the domination data.
            let mut dominatees = mem::take(&mut block_data[block_id].immediately_dominates);
            dominatees.sort_by_key(|&child| block_data[child].reverse_postorder);
            dominatees.reverse();
            block_data[block_id].immediately_dominates = dominatees;
        }

        // Fill in the within_loop information. See the docs of `within_loops` to understand what
        // we're computing.
        let mut path_dfs = DfsWithPath::new(&cfg, start_block);
        while let Some(block_id) = path_dfs.next(&cfg) {
            // Store all the loops on the path to this
            // node.
            let mut within_loops: SmallVec<_> = path_dfs
                .path
                .iter()
                .copied()
                .filter(|&loop_id| block_data[loop_id].is_loop_header)
                .collect();
            // The loops that we can reach by taking a single backward edge.
            let loops_directly_within = within_loops
                .iter()
                .copied()
                .filter(|&loop_header| {
                    cfg.neighbors_directed(loop_header, petgraph::Direction::Incoming)
                        .any(|bid| block_data[block_id].shortest_paths.contains_key(&bid))
                })
                .collect_vec();
            // The loops that we can reach by taking any number of backward edges.
            let loops_indirectly_within: HashSet<_> = loops_directly_within
                .iter()
                .copied()
                .flat_map(|loop_header| &block_data[loop_header].within_loops)
                .chain(&loops_directly_within)
                .copied()
                .collect();
            within_loops.retain(|id| loops_indirectly_within.contains(id));
            block_data[block_id].within_loops = within_loops;
        }

        let mut cfg = CfgInfo {
            cfg,
            fwd_cfg,
            loop_entries,
            switch_blocks,
            dominator_tree,
            block_data,
        };

        // Pick an exit block for each loop, if we find one.
        ExitInfo::compute_loop_exits(ctx, &mut cfg);

        // Pick an exit block for each switch, if we find one.
        ExitInfo::compute_switch_exits(&mut cfg);

        Ok(cfg)
    }

    fn block_data(&self, block_id: BlockId) -> &BlockData<'a> {
        &self.block_data[block_id]
    }
    // fn can_reach(&self, src: BlockId, tgt: BlockId) -> bool {
    //     self.block_data[src].shortest_paths.contains_key(&tgt)
    // }
    fn topo_rank(&self, block_id: BlockId) -> u32 {
        self.block_data[block_id].reverse_postorder.unwrap()
    }
    #[expect(unused)]
    fn is_backward_edge(&self, src: BlockId, tgt: BlockId) -> bool {
        self.block_data[src].reverse_postorder >= self.block_data[tgt].reverse_postorder
            && self.cfg.contains_edge(src, tgt)
    }

    /// Check if the node is within the given loop.
    fn is_within_loop(&self, loop_header: src::BlockId, block_id: src::BlockId) -> bool {
        self.block_data[block_id]
            .within_loops
            .contains(&loop_header)
    }

    /// Check if all paths from `src` to nodes in `target_set` go through `through_node`. If `src`
    /// is already in `target_set`, we ignore that empty path.
    fn all_paths_go_through(
        &self,
        src: src::BlockId,
        through_node: src::BlockId,
        target_set: &HashSet<src::BlockId>,
    ) -> bool {
        let graph = EdgeFiltered::from_fn(&self.fwd_cfg, |edge| edge.source() != through_node);
        !Dfs::new(&graph, src)
            .iter(&graph)
            .skip(1) // skip src
            .any(|bid| target_set.contains(&bid))
    }
}

impl BlockData<'_> {
    fn shortest_paths_including_self(&self) -> impl Iterator<Item = (BlockId, usize)> {
        self.shortest_paths.iter().map(|(bid, d)| (*bid, *d))
    }
    fn shortest_paths_excluding_self(&self) -> impl Iterator<Item = (BlockId, usize)> {
        self.shortest_paths_including_self()
            .filter(move |&(bid, _)| bid != self.id)
    }
    fn reachable_including_self(&self) -> impl Iterator<Item = BlockId> {
        self.shortest_paths_including_self().map(|(bid, _)| bid)
    }
    fn reachable_excluding_self(&self) -> impl Iterator<Item = BlockId> {
        self.shortest_paths_excluding_self().map(|(bid, _)| bid)
    }
    #[expect(unused)]
    fn can_reach_excluding_self(&self, other: BlockId) -> bool {
        self.shortest_paths.contains_key(&other) && self.id != other
    }
}

/// See [`ExitInfo::compute_loop_exit_ranks`].
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct LoopExitRank {
    /// Number of paths we found going to this exit.
    path_count: usize,
    /// Distance from the loop header.
    distance_from_header: Reverse<usize>,
}

impl ExitInfo {
    /// Compute the first node on each path that exits the loop.
    fn compute_loop_exit_starting_points(
        cfg: &CfgInfo,
        loop_header: src::BlockId,
    ) -> Vec<src::BlockId> {
        let mut loop_exits = Vec::new();
        // Do a dfs from the loop header while keeping track of the path from the loop header to
        // the current node.
        let mut dfs = Dfs::new(&cfg.fwd_cfg, loop_header);
        while let Some(block_id) = dfs.next(&cfg.fwd_cfg) {
            // If we've exited all the loops after and including the target one, this node is an
            // exit node for the target loop.
            if !cfg.is_within_loop(loop_header, block_id) {
                loop_exits.push(block_id);
                // Don't explore any more paths from this node.
                dfs.discovered.extend(cfg.fwd_cfg.neighbors(block_id));
            }
        }
        loop_exits
    }

    /// Compute the loop exit candidates along with a rank.
    ///
    /// In the simple case, there is one exit node through which all exit paths go. We want to be
    /// sure to catch that case, and when that's not possible we want to still find a node through
    /// which a lot of exit paths go.
    ///
    /// To do that, we first count for each exit node how many exit paths go through it, and pick
    /// the node with most occurrences. If there are many such nodes, we pick the one with shortest
    /// distance from the loop header. Finally if there are still many such nodes, we keep the
    /// first node found (the order in which we explore the graph is deterministic, and we use an
    /// insertion-order hash map).
    ///
    /// Note that exit candidates will typically be referenced more than once for one loop. This
    /// comes from the fact that whenever we reach a node outside the current loop, we register
    /// this node as well as all its children as exit candidates.
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
    fn compute_loop_exit_ranks(
        cfg: &CfgInfo,
        loop_header: src::BlockId,
    ) -> SeqHashMap<src::BlockId, LoopExitRank> {
        let mut loop_exits: SeqHashMap<BlockId, LoopExitRank> = SeqHashMap::new();
        for block_id in Self::compute_loop_exit_starting_points(cfg, loop_header) {
            for bid in cfg.block_data(block_id).reachable_including_self() {
                loop_exits
                    .entry(bid)
                    .or_insert_with(|| LoopExitRank {
                        path_count: 0,
                        distance_from_header: Reverse(
                            cfg.block_data[loop_header].shortest_paths[&bid],
                        ),
                    })
                    .path_count += 1;
            }
        }
        loop_exits
    }

    /// A loop exit is any block reachable from the loop header that isn't inside the loop.
    /// This function choses an exit for every loop. See `compute_loop_exit_ranks` for how we
    /// select them.
    ///
    /// For example:
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
    /// Once we listed all the exit candidates, we find the "best" one for every loop. The best
    /// exit is the following one:
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
    fn compute_loop_exits(ctx: &TransformCtx, cfg: &mut CfgInfo) {
        for &loop_id in &cfg.loop_entries {
            // Compute the candidates.
            let loop_exits: SeqHashMap<BlockId, LoopExitRank> =
                Self::compute_loop_exit_ranks(cfg, loop_id);
            // We choose the exit with:
            // - the most occurrences
            // - the least total distance (if there are several possibilities)
            // - doesn't necessarily lead to an error (panic, unreachable)
            let best_exits: Vec<(BlockId, LoopExitRank)> =
                loop_exits.into_iter().max_set_by_key(|&(_, rank)| rank);
            // If there is exactly one best candidate, use it. Otherwise we need to split further.
            let chosen_exit = match best_exits.into_iter().map(|(bid, _)| bid).exactly_one() {
                Ok(best_exit) => Some(best_exit),
                Err(best_exits) => {
                    // Remove the candidates which only lead to errors (panic or unreachable).
                    // If there is exactly one candidate we select it, otherwise we do not select any
                    // exit.
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
                    best_exits
                        .filter(|&bid| !cfg.block_data[bid].only_reach_error)
                        .exactly_one()
                        .map_err(|mut candidates| {
                            // Adding this sanity check so that we can see when there are several
                            // candidates.
                            let span = cfg.block_data[loop_id].contents.terminator.span;
                            sanity_check!(ctx, span, candidates.next().is_none());
                        })
                        .ok()
                }
            };
            cfg.block_data[loop_id].exit_info.loop_exit = chosen_exit;
        }
    }

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
    /// For this reason, we need to find the "exit" of the first switch, which is
    /// the point where the two branches join. Note that this can be a bit tricky,
    /// because there may be more than two branches (if we do `switch(x) { ... }`),
    /// and some of them might not join (if they contain a `break`, `panic`,
    /// `return`, etc.).
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
    fn compute_switch_exits(cfg: &mut CfgInfo) {
        // We need to give precedence to the outer switches: we thus iterate
        // over the switch blocks in topological order.
        let mut exits_set = HashSet::new();
        for bid in cfg
            .switch_blocks
            .iter()
            .copied()
            .sorted_unstable_by_key(|&bid| (cfg.topo_rank(bid), bid))
        {
            let block_data = &cfg.block_data[bid];
            // Find the best successor: this is the node with the highest flow, and the lowest
            // topological rank. If several nodes have the same flow, we want to take the highest
            // one in the hierarchy: hence the use of the topological rank.
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
            // If the switch is inside a loop, we also only consider exists that are inside that
            // same loop. There must be one, otherwise the switch entry would not be inside the
            // loop.
            let current_loop = block_data.within_loops.last().copied();
            let best_exit: Option<BlockId> = block_data
                .reachable_excluding_self()
                .filter(|&b| {
                    current_loop.is_none_or(|current_loop| cfg.is_within_loop(current_loop, b))
                })
                .max_by_key(|&id| {
                    let flow = &block_data.flow[id];
                    let rank = Reverse(cfg.topo_rank(id));
                    ((flow, rank), id)
                });
            // We have an exit candidate: we first check that it was not already taken by an
            // external switch.
            //
            // We then check that we can't reach the exit of an external switch from one of the
            // branches, without going through the exit candidate. We do this by simply checking
            // that we can't reach any of the exits of outer switches.
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
            if let Some(exit_id) = best_exit
                && !exits_set.contains(&exit_id)
                && cfg.all_paths_go_through(bid, exit_id, &exits_set)
            {
                exits_set.insert(exit_id);
                cfg.block_data[bid].exit_info.switch_exit = Some(exit_id);
            }
        }
    }
}

enum GotoKind {
    Break(usize),
    Continue(usize),
    NextBlock,
    Goto,
}

type Depth = usize;

#[derive(Debug, Clone, Copy)]
enum SpecialJump {
    /// When encountering this block, `continue` to the given depth.
    LoopContinue(Depth),
    /// When encountering this block, `break` to the given depth. This comes from a loop.
    LoopBreak(Depth),
    /// When encountering this block, `break` to the given depth. This is a `loop` context
    /// introduced only for forward jumps.
    ForwardBreak(Depth),
    /// When encountering this block, do nothing, as this is the next block that will be
    /// translated.
    NextBlock,
}

enum ReconstructMode {
    /// Reconstruct using flow heuristics.
    Flow,
    /// Reconstruct using the algorithm from "Beyond Relooper" (https://dl.acm.org/doi/10.1145/3547621).
    /// A useful invariant is that the block at the top of the jump stack is the block where
    /// control-flow will jump naturally at the end of the current block.
    Reloop,
}

struct ReconstructCtx<'a> {
    cfg: CfgInfo<'a>,
    /// The depth of `loop` contexts we may `break`/`continue` to.
    break_context_depth: Depth,
    /// Stack of block ids that should be translated to special jumps (`break`/`continue`/do
    /// nothing) in the current context.
    /// The block where control-flow continues naturally after this block is kept at the top of the
    /// stack.
    special_jump_stack: Vec<(BlockId, SpecialJump)>,
    mode: ReconstructMode,
}

impl<'a> ReconstructCtx<'a> {
    fn build(ctx: &TransformCtx, src_body: &'a src::ExprBody) -> Result<Self, Irreducible> {
        // Compute all sorts of graph-related information about the control-flow graph, including
        // reachability, the dominator tree, loop entries, and loop/switch exits.
        let cfg = CfgInfo::build(ctx, &src_body.body)?;

        // Translate the body by reconstructing the loops and the
        // conditional branchings.
        let use_relooper = true;
        Ok(ReconstructCtx {
            cfg,
            break_context_depth: 0,
            special_jump_stack: Vec::new(),
            mode: if use_relooper {
                ReconstructMode::Reloop
            } else {
                ReconstructMode::Flow
            },
        })
    }

    fn translate_statement(&self, st: &src::Statement) -> tgt::Statement {
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
        };
        tgt::Statement::new(src_span, st)
    }

    fn get_goto_kind(&self, target_block: src::BlockId) -> GotoKind {
        match self
            .special_jump_stack
            .iter()
            .rev()
            .enumerate()
            .find(|(_, (b, _))| *b == target_block)
        {
            Some((i, (_, jump_target))) => match jump_target {
                // The top of the stack is where control-flow goes naturally, no need to add a
                // `break`/`continue`.
                SpecialJump::LoopContinue(_) | SpecialJump::ForwardBreak(_)
                    if i == 0 && matches!(self.mode, ReconstructMode::Reloop) =>
                {
                    GotoKind::NextBlock
                }
                SpecialJump::LoopContinue(depth) => {
                    GotoKind::Continue(self.break_context_depth - depth)
                }
                SpecialJump::ForwardBreak(depth) | SpecialJump::LoopBreak(depth) => {
                    GotoKind::Break(self.break_context_depth - depth)
                }
                SpecialJump::NextBlock => GotoKind::NextBlock,
            },
            // Translate the block without a jump.
            None => GotoKind::Goto,
        }
    }

    /// Translate a jump to the given block. The span is used to create the jump statement, if any.
    fn translate_jump(&mut self, span: Span, target_block: src::BlockId) -> tgt::Block {
        let st = match self.get_goto_kind(target_block) {
            GotoKind::Break(index) => tgt::StatementKind::Break(index),
            GotoKind::Continue(index) => tgt::StatementKind::Continue(index),
            GotoKind::NextBlock => tgt::StatementKind::Nop,
            // "Standard" goto: we recursively translate the block.
            GotoKind::Goto => return self.translate_block(target_block),
        };
        tgt::Statement::new(span, st).into_block()
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
                let mut block = self.translate_jump(terminator.span, *target);
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
                let mut block = self.translate_jump(terminator.span, *target);
                block.statements.insert(0, st);
                block
            }
            src::TerminatorKind::Goto { target } => self.translate_jump(terminator.span, *target),
            src::TerminatorKind::Switch { discr, targets } => {
                // Translate the target expressions
                let switch = match &targets {
                    src::SwitchTargets::If(then_tgt, else_tgt) => {
                        let then_block = self.translate_jump(terminator.span, *then_tgt);
                        let else_block = self.translate_jump(terminator.span, *else_tgt);
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
                        let mut branches: SeqHashMap<src::BlockId, (Vec<Literal>, tgt::Block)> =
                            SeqHashMap::new();

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
                                let block = self.translate_jump(terminator.span, *bid);
                                // We use the terminator span information in case then
                                // then statement is `None`
                                branches.insert(*bid, (vec![v.clone()], block));
                            }
                        }
                        let targets_blocks: Vec<(Vec<Literal>, tgt::Block)> =
                            branches.into_iter().map(|(_, x)| x).collect();

                        let otherwise_block = self.translate_jump(terminator.span, *otherwise);

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

    /// Translate just the block statements and terminator.
    fn translate_block_itself(&mut self, block_id: src::BlockId) -> tgt::Block {
        let block = self.cfg.block_data[block_id].contents;
        // Translate the statements inside the block
        let statements = block
            .statements
            .iter()
            .map(|st| self.translate_statement(st))
            .collect_vec();
        // Translate the terminator.
        let terminator = self.translate_terminator(&block.terminator);
        // Prepend the statements to the terminator.
        if let Some(st) = tgt::Block::from_seq(statements) {
            st.merge(terminator)
        } else {
            terminator
        }
    }

    /// Translate a block including surrounding control-flow like looping.
    fn translate_block(&mut self, block_id: src::BlockId) -> tgt::Block {
        ensure_sufficient_stack(|| self.translate_block_inner(block_id))
    }
    fn translate_block_inner(&mut self, block_id: src::BlockId) -> tgt::Block {
        // Some of the blocks we might jump to inside this tree can't be translated as normal
        // blocks: the loop backward edges must become `continue`s and the merge nodes may need
        // some care if we're jumping to them from distant locations.
        // For this purpose, we push to the `special_jump_stack` the block ids that must be
        // translated specially. In `translate_jump` we check the stack. At the end of this
        // function we restore the stack to its previous state.
        let old_context_depth = self.special_jump_stack.len();
        let block_data = &self.cfg.block_data[block_id];
        let span = block_data.contents.terminator.span;

        // Catch jumps to the loop header or loop exit.
        if block_data.is_loop_header {
            self.break_context_depth += 1;
            if let Some(exit_id) = block_data.exit_info.loop_exit {
                self.special_jump_stack
                    .push((exit_id, SpecialJump::LoopBreak(self.break_context_depth)));
            }
            // Put the next block at the top of the stack.
            self.special_jump_stack.push((
                block_id,
                SpecialJump::LoopContinue(self.break_context_depth),
            ));
        }

        // Catch jumps to a merge node.
        if let ReconstructMode::Reloop = self.mode {
            // We support forward-jumps using `break`
            // The child with highest postorder numbering is nested outermost in this scheme.
            let merge_children = block_data
                .immediately_dominates
                .iter()
                .copied()
                .filter(|&child| self.cfg.block_data[child].is_merge_target);
            for child in merge_children {
                self.break_context_depth += 1;
                self.special_jump_stack
                    .push((child, SpecialJump::ForwardBreak(self.break_context_depth)));
            }
        }

        // Move some code that would be inside one or several switch branches to be after the
        // switch intead.
        if let Some(bid) = block_data.exit_info.switch_exit
            && !block_data.is_loop_header
        {
            self.special_jump_stack.push((bid, SpecialJump::NextBlock));
        }

        // Translate this block. Any jumps to a loop header or a merge node will be replaced with
        // `continue`/`break`.
        let mut block = self.translate_block_itself(block_id);

        // Reset the state to what it was previously, and translate what remains.
        let new_block = move |kind| tgt::Statement::new(block.span, kind).into_block();
        while self.special_jump_stack.len() > old_context_depth {
            match self.special_jump_stack.pop().unwrap() {
                (_loop_header, SpecialJump::LoopContinue(_)) => {
                    self.break_context_depth -= 1;
                    block = new_block(tgt::StatementKind::Loop(block));
                }
                (next_block, SpecialJump::ForwardBreak(_)) => {
                    self.break_context_depth -= 1;
                    // We add a `loop { ...; break }` so that we can use `break` to jump forward.
                    block = block.merge(new_block(tgt::StatementKind::Break(0)));
                    block = new_block(tgt::StatementKind::Loop(block));
                    // We must translate the merge nodes after the block used for forward jumps to
                    // them.
                    let next_block = self.translate_jump(span, next_block);
                    block = block.merge(next_block);
                }
                (next_block, SpecialJump::NextBlock) | (next_block, SpecialJump::LoopBreak(..)) => {
                    let next_block = self.translate_jump(span, next_block);
                    block = block.merge(next_block);
                }
            }
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
    let start_block = BlockId::ZERO;
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
    let tgt_body = ctx.translate_block(start_block);

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

        if ctx.options.print_built_llbc {
            eprintln!("# LLBC resulting from control-flow reconstruction:\n\n{ctx}\n",);
        } else {
            trace!("# LLBC resulting from control-flow reconstruction:\n\n{ctx}\n",);
        }
    }
}
