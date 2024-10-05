//! Utilities to generate error reports about the external dependencies.
use crate::ast::{AnyTransId, Span};
use crate::formatter::{FmtCtx, Formatter};
use macros::VariantIndexArity;
use petgraph::algo::dijkstra::dijkstra;
use petgraph::graphmap::DiGraphMap;
use rustc_error_messages::MultiSpan;
use rustc_errors::DiagCtxtHandle;
use std::cmp::{Ord, PartialOrd};
use std::collections::{HashMap, HashSet};

/// Common error used during the translation.
#[derive(Debug)]
pub struct Error {
    pub span: Span,
    pub msg: String,
}

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
        let e = $crate::errors::Error {
            span: $span,
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
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DepSource {
    pub src_id: AnyTransId,
    /// The location where the id was referred to. We store `None` for external dependencies as we
    /// don't want to show these to the users.
    pub span: Option<Span>,
}

/// The context for tracking and reporting errors.
pub struct ErrorCtx<'ctx> {
    /// If true, do not abort on the first error and attempt to extract as much as possible.
    pub continue_on_failure: bool,
    /// If true, print the errors as warnings, and do not abort.
    pub errors_as_warnings: bool,

    /// The compiler session, used for displaying errors.
    pub dcx: DiagCtxtHandle<'ctx>,
    /// The ids of the external_declarations for which extraction we encountered errors.
    pub external_decls_with_errors: HashSet<AnyTransId>,
    /// The ids of the declarations we completely failed to extract and had to ignore.
    pub ignored_failed_decls: HashSet<AnyTransId>,
    /// For each external item, a list of locations that point to it. See [DepSource].
    pub external_dep_sources: HashMap<AnyTransId, HashSet<DepSource>>,
    /// The id of the definition we are exploring, used to track the source of errors.
    pub def_id: Option<AnyTransId>,
    /// Whether the definition being explored is local to the crate or not.
    pub def_id_is_local: bool,
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
    pub fn span_err(&mut self, span: Span, msg: &str) {
        self.span_err_no_register(span, msg);
        self.error_count += 1;
        if let Some(id) = self.def_id
            && !self.def_id_is_local
        {
            let _ = self.external_decls_with_errors.insert(id);
        }
    }

    pub fn ignore_failed_decl(&mut self, id: AnyTransId) {
        self.ignored_failed_decls.insert(id);
    }
}

/// For tracing error dependencies.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, VariantIndexArity)]
enum Node {
    External(AnyTransId),
    /// We use the span information only for local references
    Local(AnyTransId, Span),
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
    pub fn report_external_deps_errors(&self, f: FmtCtx<'_>) {
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

        trace!("dep_sources:\n{:?}", self.external_dep_sources);
        for (id, srcs) in &self.external_dep_sources {
            let src_node = Node::External(*id);
            graph.insert_node(src_node);

            for src in srcs {
                let tgt_node = match src.span {
                    Some(span) => Node::Local(src.src_id, span),
                    None => Node::External(src.src_id),
                };
                graph.insert_edge(src_node, tgt_node)
            }
        }
        trace!("Graph:\n{}", graph);

        // We need to compute the reachability graph. An easy way is simply
        // to use Dijkstra on every external definition which triggered an
        // error.
        for id in &self.external_decls_with_errors {
            let reachable = dijkstra(&graph.dgraph, Node::External(*id), None, &mut |_| 1);
            trace!("id: {:?}\nreachable:\n{:?}", id, reachable);

            let reachable: Vec<rustc_span::Span> = reachable
                .iter()
                .filter_map(|(n, _)| match n {
                    Node::External(_) => None,
                    Node::Local(_, span) => Some(span.rust_span()),
                })
                .collect();

            // Display the error message
            let span = MultiSpan::from_spans(reachable);
            let msg = format!(
                "The external definition `{}` triggered errors. \
                It is (transitively) used at the following location(s):",
                f.format_object(*id)
            );
            self.span_err_no_register(span, &msg);
        }
    }
}
