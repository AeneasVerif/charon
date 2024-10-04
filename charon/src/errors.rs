//! Utilities to generate error reports about the external dependencies.
use crate::ast::Span;
use macros::VariantIndexArity;
use petgraph::algo::dijkstra::dijkstra;
use petgraph::graphmap::DiGraphMap;
use rustc_error_messages::MultiSpan;
use rustc_errors::DiagCtxtHandle;
use rustc_span::def_id::DefId;
use std::cmp::{Ord, PartialOrd};
use std::collections::{HashMap, HashSet};

#[macro_export]
macro_rules! register_error_or_panic {
    ($ctx:expr, $span: expr, $msg: expr) => {{
        $ctx.span_err($span, &$msg);
        if !$ctx.continue_on_failure() {
            panic!("{}", $msg);
        }
    }};
}
pub use register_error_or_panic;

/// Macro to either panic or return on error, depending on the CLI options
#[macro_export]
macro_rules! error_or_panic {
    ($ctx:expr, $span:expr, $msg:expr) => {{
        $crate::errors::register_error_or_panic!($ctx, $span, $msg);
        let e = $crate::common::Error {
            span: $span.into(),
            msg: $msg.to_string(),
        };
        return Err(e);
    }};
}
pub use error_or_panic;

/// Custom assert to either panic or return an error
#[macro_export]
macro_rules! error_assert {
    ($ctx:expr, $span: expr, $b: expr) => {
        if !$b {
            let msg = format!("assertion failure: {:?}", stringify!($b));
            $crate::errors::error_or_panic!($ctx, $span, msg);
        }
    };
    ($ctx:expr, $span: expr, $b: expr, $msg: expr) => {
        if !$b {
            $crate::errors::error_or_panic!($ctx, $span, $msg);
        }
    };
}
pub use error_assert;

/// We use this to save the origin of an id. This is useful for the external
/// dependencies, especially if some external dependencies don't extract:
/// we use this information to tell the user what is the code which
/// (transitively) lead to the extraction of those problematic dependencies.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct DepSource {
    pub src_id: DefId,
    pub span: rustc_span::Span,
}

impl DepSource {
    /// Value with which we order `DepSource`s.
    fn sort_key(&self) -> impl Ord {
        (self.src_id.index, self.src_id.krate)
    }
}

/// Manual impls because `DefId` is not orderable.
impl PartialOrd for DepSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DepSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
}

impl DepSource {
    pub fn make(src_id: DefId, span: Span) -> Option<Self> {
        Some(DepSource {
            src_id,
            span: span.rust_span(),
        })
    }
}

/// The context for tracking and reporting errors.
pub struct ErrorCtx<'ctx> {
    /// If true, do not abort on the first error and attempt to extract as much as possible.
    pub continue_on_failure: bool,
    /// If true, print the errors as warnings, and do not abort.
    pub errors_as_warnings: bool,

    /// The compiler session, used for displaying errors.
    pub dcx: DiagCtxtHandle<'ctx>,
    /// The ids of the declarations for which extraction we encountered errors.
    pub decls_with_errors: HashSet<DefId>,
    /// The ids of the declarations we completely failed to extract and had to ignore.
    pub ignored_failed_decls: HashSet<DefId>,
    /// Dependency graph with sources. See [DepSource].
    pub dep_sources: HashMap<DefId, HashSet<DepSource>>,
    /// The id of the definition we are exploring, used to track the source of errors.
    pub def_id: Option<DefId>,
    /// The number of errors encountered so far.
    pub error_count: usize,
}

impl ErrorCtx<'_> {
    pub fn continue_on_failure(&self) -> bool {
        self.continue_on_failure
    }
    pub(crate) fn has_errors(&self) -> bool {
        self.error_count > 0
    }

    /// Report an error without registering anything.
    pub(crate) fn span_err_no_register<S: Into<MultiSpan>>(&self, span: S, msg: &str) {
        let msg = msg.to_string();
        if self.errors_as_warnings {
            self.dcx.span_warn(span, msg);
        } else {
            self.dcx.span_err(span, msg);
        }
    }

    /// Report and register an error.
    pub fn span_err<S: Into<MultiSpan>>(&mut self, span: S, msg: &str) {
        self.span_err_no_register(span, msg);
        self.error_count += 1;
        if let Some(id) = self.def_id {
            let _ = self.decls_with_errors.insert(id);
        }
    }

    /// Register the fact that `id` is a dependency of `src` (if `src` is not `None`).
    pub fn register_dep_source(&mut self, src: &Option<DepSource>, id: DefId) {
        if let Some(src) = src {
            if src.src_id != id {
                match self.dep_sources.get_mut(&id) {
                    None => {
                        let _ = self.dep_sources.insert(id, HashSet::from([*src]));
                    }
                    Some(srcs) => {
                        let _ = srcs.insert(*src);
                    }
                }
            }
        }
    }

    pub fn ignore_failed_decl(&mut self, id: DefId) {
        self.ignored_failed_decls.insert(id);
    }
}

/// For tracing error dependencies.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, VariantIndexArity)]
enum Node {
    External(DefId),
    /// We use the span information only for local references
    Local(DefId, rustc_span::Span),
}

impl Node {
    /// Value with which we order `Node`s.
    fn sort_key(&self) -> impl Ord {
        let (variant_index, _) = self.variant_index_arity();
        let (Self::External(def_id) | Self::Local(def_id, _)) = self;
        (variant_index, def_id.index, def_id.krate)
    }
}

/// Manual impls because `DefId` is not orderable.
impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Node {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
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

impl ErrorCtx<'_> {
    /// In case errors happened when extracting the definitions coming from
    /// the external dependencies, print a detailed report to explain
    /// to the user which dependencies were problematic, and where they
    /// are used in the code.
    pub fn report_external_deps_errors(&self) {
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

        trace!("dep_sources:\n{:?}", self.dep_sources);
        for (id, srcs) in &self.dep_sources {
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
        for id in &self.decls_with_errors {
            if !id.is_local() {
                let reachable = dijkstra(&graph.dgraph, Node::External(*id), None, &mut |_| 1);
                trace!("id: {:?}\nreachable:\n{:?}", id, reachable);

                let reachable: Vec<rustc_span::Span> = reachable
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
