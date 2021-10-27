//! IM to CFIM (Control-Flow Internal MIR)

use crate::cfim_ast as tgt;
use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::im_ast as src;
use crate::translate_functions_to_im::FunTransContext;
use crate::types::*;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use im;
use im::{OrdMap, OrdSet, Vector};
use macros::{EnumAsGetters, EnumIsA, VariantName};
use petgraph::algo::dominators::simple_fast;
use petgraph::algo::{tarjan_scc, toposort};
use petgraph::graphmap::DiGraphMap;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;
use std::ops::Deref;

pub type Decls = tgt::FunDecls;

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId::Id, ()>;

/// Build the Control-Flow Graph of a function body
fn build_cfg(body: &src::Body) -> Cfg {
    let mut cfg = Cfg::new();

    // Add the nodes
    for block_id in body.blocks.iter_indices() {
        cfg.add_node(block_id);
    }

    // Add the edges
    let mut explored = HashSet::new();
    build_cfg_edges(&mut cfg, &mut explored, body, src::BlockId::ZERO);

    cfg
}

/// Build the CFG for a part of the body, and where we ignore the gotos to
/// the root (those gotos are backward edges).
fn build_part_cfg(body: &src::Body, root: src::BlockId::Id, part: &Vec<src::BlockId::Id>) -> Cfg {
    let mut cfg = Cfg::new();

    // Add the nodes
    for block_id in body.blocks.iter_indices() {}
    for block_id in body.blocks.iter_indices() {
        cfg.add_node(block_id);
    }

    // Add the edges
    let mut explored = HashSet::new();
    build_cfg_edges(&mut cfg, &mut explored, body, src::BlockId::ZERO);

    // TODO: we explore the whole cfg here...
    unimplemented!();

    cfg
}

fn get_block_targets(body: &src::Body, block_id: src::BlockId::Id) -> Vec<src::BlockId::Id> {
    let block = body.blocks.get(block_id).unwrap();

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

/// TODO: remove
fn block_goes_directly_to_exit(
    body: &src::Body,
    directly_exit: &HashSet<src::BlockId::Id>,
    block_id: src::BlockId::Id,
) -> bool {
    let block = body.blocks.get(block_id).unwrap();

    match &block.terminator {
        src::Terminator::Goto { target: _ }
        | src::Terminator::Switch {
            discr: _,
            targets: _,
        } => false,
        src::Terminator::Panic | src::Terminator::Unreachable | src::Terminator::Return => true,
        src::Terminator::Drop { place: _, target }
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
        } => directly_exit.contains(target),
    }
}

fn build_cfg_edges(
    cfg: &mut Cfg,
    explored: &mut HashSet<src::BlockId::Id>,
    body: &src::Body,
    block_id: src::BlockId::Id,
) {
    // Check if we already explored this node (there may be loops)
    if explored.contains(&block_id) {
        return;
    }
    explored.insert(block_id);

    // Retrieve the block targets
    let targets = get_block_targets(body, block_id);

    // Add edges for all the targets
    for tgt in &targets {
        cfg.add_edge(block_id, *tgt, ());
    }

    // Explore the targets
    for tgt in &targets {
        build_cfg_edges(cfg, explored, body, *tgt);
    }
}

/// This structure contains the CFG for a function body, where all the backward
/// edges have been removed.
struct CfgNoBackEdges {
    pub cfg: Cfg,
    /// We consider the destination of the backward edges to be loop entries and
    /// store them here.
    pub loop_entries: HashSet<src::BlockId::Id>,
    /// The blocks whose terminators are a switch are stored here.
    pub switch_blocks: HashSet<src::BlockId::Id>,
    /// The blocks from where we directly go to back-edge, return or panic,
    /// without going through any goto or switch.
    /// TODO: remove
    pub directly_exit: HashSet<src::BlockId::Id>,
}

fn build_cfg_no_back_edges(body: &src::Body) -> CfgNoBackEdges {
    let mut cfg = CfgNoBackEdges {
        cfg: Cfg::new(),
        loop_entries: HashSet::new(),
        switch_blocks: HashSet::new(),
        directly_exit: HashSet::new(),
    };

    // Add the nodes
    for block_id in body.blocks.iter_indices() {
        cfg.cfg.add_node(block_id);
    }

    // Add the edges
    let previous = im::HashSet::new();
    build_cfg_no_back_edges_edges(&mut cfg, &previous, body, src::BlockId::ZERO);

    cfg
}

fn block_is_switch(body: &src::Body, block_id: src::BlockId::Id) -> bool {
    let block = body.blocks.get(block_id).unwrap();
    block.terminator.is_switch()
}

fn build_cfg_no_back_edges_edges(
    cfg: &mut CfgNoBackEdges,
    previous: &im::HashSet<src::BlockId::Id>,
    body: &src::Body,
    block_id: src::BlockId::Id,
) {
    // Insert the current block in the set of previous blocks
    let mut previous = previous.clone();
    previous.insert(block_id);

    // Check if it is a switch
    if block_is_switch(body, block_id) {
        cfg.switch_blocks.insert(block_id);
    }

    // Retrieve the block targets
    let targets = get_block_targets(body, block_id);

    // Add edges for all the targets and explore them, if they are not predecessors
    for tgt in &targets {
        if previous.contains(tgt) {
            // This is a backward edge
            cfg.loop_entries.insert(*tgt);
        } else {
            // Not a backward edge: insert the edge and explore
            cfg.cfg.add_edge(block_id, *tgt, ());
            build_cfg_no_back_edges_edges(cfg, &previous, body, *tgt);
        }
    }

    // Check if we directly go to an exit point from there
    if block_goes_directly_to_exit(body, &cfg.directly_exit, block_id) {
        cfg.directly_exit.insert(block_id);
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

/// Explanations: TODO
fn find_filtered_successors(
    cfg: &CfgNoBackEdges,
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
    let children: Vec<src::BlockId::Id> = Vec::from_iter(cfg.cfg.neighbors(block_id));
    let mut children_succs: Vec<im::OrdSet<OrdBlockId>> = Vec::from_iter(
        children
            .iter()
            .map(|bid| find_filtered_successors(cfg, tsort_map, memoized, *bid)),
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

fn compute_loop_switch_exits(
    cfg: &CfgNoBackEdges,
    tsort_map: &HashMap<src::BlockId::Id, usize>,
) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
    // Compute the filtered successors map, starting at the root node
    let mut fsuccs_map = HashMap::new();
    let _ = find_filtered_successors(cfg, tsort_map, &mut fsuccs_map, src::BlockId::ZERO);

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

fn get_loop_index_if_backward(next_block_id: src::BlockId::Id) -> Option<usize> {
    unimplemented!();
}

fn get_loop_index_if_break(next_block_id: src::BlockId::Id) -> Option<usize> {
    unimplemented!();
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
        if next_block_id == *loop_id {
            return GotoKind::Continue(i);
        } else {
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
    if current_exit_block == Some(next_block_id) {
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
    cfg: &CfgNoBackEdges,
    body: &src::Body,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    mut parent_loops: Vector<src::BlockId::Id>,
    mut current_exit_block: Option<src::BlockId::Id>,
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
                body,
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
    cfg: &CfgNoBackEdges,
    body: &src::Body,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    mut parent_loops: Vector<src::BlockId::Id>,
    mut current_exit_block: Option<src::BlockId::Id>,
    block_id: src::BlockId::Id,
    terminator: &src::Terminator,
) -> Option<tgt::Expression> {
    match terminator {
        src::Terminator::Panic | src::Terminator::Unreachable => {
            Some(tgt::Expression::Statement(tgt::Statement::Panic))
        }
        src::Terminator::Return => Some(tgt::Expression::Statement(tgt::Statement::Return)),
        src::Terminator::Goto { target } => translate_child_expression(
            cfg,
            body,
            exits_map,
            parent_loops,
            current_exit_block,
            *target,
        ),
        src::Terminator::Drop { place, target } => {
            let opt_child = translate_child_expression(
                cfg,
                body,
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
                body,
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
                body,
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
                        body,
                        exits_map,
                        parent_loops.clone(),
                        current_exit_block,
                        *then_tgt,
                    );
                    let then_exp = opt_expression_to_nop(then_exp);
                    let else_exp = translate_child_expression(
                        cfg,
                        body,
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
                            body,
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
                        body,
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

fn translate_expression(
    cfg: &CfgNoBackEdges,
    body: &src::Body,
    exits_map: &HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    parent_loops: Vector<src::BlockId::Id>,
    current_exit_block: Option<src::BlockId::Id>,
    block_id: src::BlockId::Id,
) -> Option<tgt::Expression> {
    let block = body.blocks.get(block_id).unwrap();

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
        body,
        exits_map,
        nparent_loops,
        ncurrent_exit_block,
        block_id,
        &block.terminator,
    );

    // Translate the statements
    let statements = Vec::from_iter(
        block
            .statements
            .iter()
            .filter_map(|st| translate_statement(st)),
    );

    // Put the statements and the terminator together
    let exp = combine_statements_and_expression(statements, terminator);

    // If we just translated a loop or a switch, and there is an exit block,
    // we need to translate the exit block and concatenate the two expressions
    // we have as a sequence
    if (is_loop || is_switch) && current_exit_block.is_some() {
        let exit_block_id = current_exit_block.unwrap();
        let next_exp = translate_expression(
            cfg,
            body,
            exits_map,
            parent_loops,
            current_exit_block,
            exit_block_id,
        );
        combine_expressions(exp, next_exp)
    } else {
        exp
    }
}

fn translate_function(im_ctx: &FunTransContext, src_decl_id: DefId::Id) -> tgt::FunDecl {
    // Retrieve the function declaration
    let src_decl = im_ctx.decls.get(src_decl_id).unwrap();

    // Explore the function body to create the control-flow graph without backward
    // edges, and identify the loop entries (which are destinations of backward edges).
    let cfg_no_be = build_cfg_no_back_edges(&src_decl.body);

    // Use the CFG without backward edges to topologically sort the nodes.
    // Note that `toposort` returns `Err` if and only if it finds cycles (which
    // can't happen).
    let tsorted: Vec<src::BlockId::Id> = toposort(&cfg_no_be.cfg, None).unwrap();

    // Build the map: block id -> topological sort rank
    let tsort_map: HashMap<src::BlockId::Id, usize> = HashMap::from_iter(
        tsorted
            .into_iter()
            .enumerate()
            .map(|(i, block_id)| (block_id, i)),
    );

    // Find the exit block for all the loops and switches, if such an exit point
    // exists.
    let exits_map = compute_loop_switch_exits(&cfg_no_be, &tsort_map);

    // Translate the body by reconstructing the loops and the conditional branchings.
    // Note that we shouldn't get `None`.
    let body_exp = translate_expression(
        &cfg_no_be,
        &src_decl.body,
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
        arg_count: src_decl.body.arg_count,
        locals: src_decl.body.locals.clone(),
        body: body_exp,
    }
}

// TODO: reducible graphs
pub fn translate_functions(im_ctx: &FunTransContext) -> Decls {
    let mut out_decls = DefId::Vector::new();

    for src_decl_id in im_ctx.decls.iter_indices() {
        out_decls.push_back(translate_function(im_ctx, src_decl_id));
    }

    out_decls
}
