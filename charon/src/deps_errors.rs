//! Utilities to generate error reports about the external dependencies.
use crate::translate_ctx::*;
use petgraph::algo::dijkstra::dijkstra;
use petgraph::graphmap::DiGraphMap;
use rustc_error_messages::MultiSpan;
use rustc_hir::def_id::DefId;
use rustc_span::Span;

/// For error reporting
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Node {
    External(DefId),
    /// We use the span information only for local references
    Local(DefId, Span),
}

struct Graph {
    dgraph: DiGraphMap<Node, ()>,
}

impl std::fmt::Display for Graph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        for (from, to, _) in self.dgraph.all_edges() {
            writeln!(f, "{from:?} -> {to:?}")?
        }
        Ok(())
    }
}

impl Graph {
    fn new() -> Self {
        Graph {
            dgraph: DiGraphMap::new(),
        }
    }

    fn insert_node(&mut self, n: Node) {
        // We have to be careful about duplicate nodes
        if !self.dgraph.contains_node(n) {
            self.dgraph.add_node(n);
        }
    }

    fn insert_edge(&mut self, from: Node, to: Node) {
        self.insert_node(from);
        self.insert_node(to);
        if !self.dgraph.contains_edge(from, to) {
            self.dgraph.add_edge(from, to, ());
        }
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// In case errors happened when extracting the definitions coming from
    /// the external dependencies, print a detailed report to explain
    /// to the user which dependencies were problematic, and where they
    /// are used in the code.
    pub(crate) fn report_external_deps_errors(&self) {
        if !self.has_errors() {
            return;
        }

        // Create a dependency graph, with spans.
        // We want to know what are the usages in the source code which
        // lead to the extraction of the problematic definitions. For this
        // reason, we only include edges:
        // - from external def to external def
        // - from local def to external def
        let mut graph = Graph::new();

        trace!("dep_sources:\n{:?}", self.translated.dep_sources);
        for (id, srcs) in &self.translated.dep_sources {
            // Only insert dependencies from external defs
            if !id.is_local() {
                let node = Node::External(*id);
                graph.insert_node(node);

                for src in srcs {
                    if src.src_id.is_local() {
                        graph.insert_edge(node, Node::Local(src.src_id, src.span));
                    } else {
                        graph.insert_edge(node, Node::External(src.src_id));
                    }
                }
            }
        }
        trace!("Graph:\n{}", graph);

        // We need to compute the reachability graph. An easy way is simply
        // to use Dijkstra on every external definition which triggered an
        // error.
        for id in &self.translated.decls_with_errors {
            if !id.is_local() {
                let reachable = dijkstra(&graph.dgraph, Node::External(*id), None, &mut |_| 1);
                trace!("id: {:?}\nreachable:\n{:?}", id, reachable);

                let reachable: Vec<Span> = reachable
                    .iter()
                    .filter_map(|(n, _)| match n {
                        Node::External(_) => None,
                        Node::Local(_, span) => Some(*span),
                    })
                    .collect();

                // Display the error message
                let span = MultiSpan::from_spans(reachable);
                let msg = format!("The external definition `{:?}` triggered errors. It is (transitively) used at the following location(s):",
                *id,
                );
                self.span_err_no_register(span, &msg);
            }
        }
    }
}
