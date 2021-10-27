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
use im::{OrdMap, OrdSet, Vector};
use macros::{EnumAsGetters, EnumIsA, VariantName};
use petgraph::algo::dominators::simple_fast;
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use std::collections::HashSet;
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
        src::Terminator::Switch { discr, targets } => match targets {
            src::SwitchTargets::If(then_tgt, else_tgt) => {
                vec![*then_tgt, *else_tgt]
            }
            src::SwitchTargets::SwitchInt(_, targets, otherwise) => {
                let mut all_targets = vec![];
                for (_, target) in targets {
                    all_targets.push(*target);
                }
                all_targets.push(*otherwise);
                all_targets
            }
        },
        src::Terminator::Panic | src::Terminator::Unreachable | src::Terminator::Return => {
            vec![]
        }
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

fn translate_function(im_ctx: &FunTransContext, src_decl_id: DefId::Id) -> Result<tgt::FunDecl> {
    // Retrieve the function declaration
    let src_decl = im_ctx.decls.get(src_decl_id).unwrap();

    // Explore the function body to create the control-flow graph
    let cfg = build_cfg(&src_decl.body);

    // Analyze the graph to look for dominators and strongly connected components (loops)
    let sccs = tarjan_scc(&cfg);
    let dominators = simple_fast(&cfg, src::BlockId::ZERO);

    // Find the loops and the conditional branchings
    unimplemented!();
}

// TODO: reducible graphs
pub fn translate_functions(im_ctx: &FunTransContext) -> Result<Decls> {
    let mut out_decls = DefId::Vector::new();

    for src_decl_id in im_ctx.decls.iter_indices() {
        out_decls.push_back(translate_function(im_ctx, src_decl_id)?);
    }

    Ok(out_decls)
}
