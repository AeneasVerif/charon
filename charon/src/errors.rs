//! Utilities to generate error reports about the external dependencies.
use crate::ast::*;
use macros::VariantIndexArity;
use petgraph::prelude::DiGraphMap;
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
    ($ctx:expr, $krate:expr, $span: expr, $msg: expr) => {{
        $ctx.span_err($krate, $span, &$msg);
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
    ($ctx:expr, $krate:expr, $span:expr, $msg:expr) => {{
        $crate::errors::register_error_or_panic!($ctx, $krate, $span, $msg);
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

/// For tracing error dependencies.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, VariantIndexArity)]
enum DepNode {
    External(AnyTransId),
    /// We use the span information only for local references
    Local(AnyTransId, Span),
}

/// Graph of dependencies between erroring definitions and the definitions they came from.
struct DepGraph {
    dgraph: DiGraphMap<DepNode, ()>,
}

impl DepGraph {
    fn new() -> Self {
        DepGraph {
            dgraph: DiGraphMap::new(),
        }
    }

    fn insert_node(&mut self, n: DepNode) {
        // We have to be careful about duplicate nodes
        if !self.dgraph.contains_node(n) {
            self.dgraph.add_node(n);
        }
    }

    fn insert_edge(&mut self, from: DepNode, to: DepNode) {
        self.insert_node(from);
        self.insert_node(to);
        if !self.dgraph.contains_edge(from, to) {
            self.dgraph.add_edge(from, to, ());
        }
    }
}

impl std::fmt::Display for DepGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        for (from, to, _) in self.dgraph.all_edges() {
            writeln!(f, "{from:?} -> {to:?}")?
        }
        Ok(())
    }
}

/// The context for tracking and reporting errors.
pub struct ErrorCtx<'ctx> {
    /// If true, do not abort on the first error and attempt to extract as much as possible.
    pub continue_on_failure: bool,
    /// If true, print the warnings as errors, and abort if any errors were raised.
    pub error_on_warnings: bool,

    /// The compiler session, used for displaying errors.
    #[cfg(feature = "rustc")]
    pub dcx: rustc_errors::DiagCtxtHandle<'ctx>,
    #[cfg(not(feature = "rustc"))]
    pub dcx: &'ctx (),
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
    #[cfg(feature = "rustc")]
    pub fn span_err_no_register(
        &self,
        _krate: &TranslatedCrate,
        span: impl Into<rustc_error_messages::MultiSpan>,
        msg: &str,
    ) {
        let msg = msg.to_string();
        if self.error_on_warnings {
            self.dcx.span_err(span, msg);
        } else {
            self.dcx.span_warn(span, msg);
        }
    }
    #[cfg(not(feature = "rustc"))]
    pub(crate) fn span_err_no_register(&self, _krate: &TranslatedCrate, _span: Span, msg: &str) {
        let msg = msg.to_string();
        if self.error_on_warnings {
            error!("{}", msg);
        } else {
            warn!("{}", msg);
        }
    }

    /// Report and register an error.
    pub fn span_err(&mut self, krate: &TranslatedCrate, span: Span, msg: &str) {
        self.span_err_no_register(krate, span, msg);
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

    /// Register the fact that `id` is a dependency of `src` (if `src` is not `None`).
    pub fn register_dep_source(
        &mut self,
        src: &Option<DepSource>,
        item_id: AnyTransId,
        is_local: bool,
    ) {
        if let Some(src) = src {
            if src.src_id != item_id && !is_local {
                self.external_dep_sources
                    .entry(item_id)
                    .or_default()
                    .insert(*src);
            }
        }
    }
}

impl ErrorCtx<'_> {
    /// In case errors happened when extracting the definitions coming from
    /// the external dependencies, print a detailed report to explain
    /// to the user which dependencies were problematic, and where they
    /// are used in the code.
    #[cfg(feature = "rustc")]
    pub fn report_external_deps_errors(&self, f: crate::formatter::FmtCtx<'_>) {
        use crate::formatter::Formatter;
        use petgraph::algo::dijkstra::dijkstra;
        use rustc_error_messages::MultiSpan;

        if !self.has_errors() {
            return;
        }
        // Create a dependency graph, with spans.
        // We want to know what are the usages in the source code which
        // lead to the extraction of the problematic definitions. For this
        // reason, we only include edges:
        // - from external def to external def
        // - from local def to external def
        let mut graph = DepGraph::new();

        trace!("dep_sources:\n{:?}", self.external_dep_sources);
        for (id, srcs) in &self.external_dep_sources {
            let src_node = DepNode::External(*id);
            graph.insert_node(src_node);

            for src in srcs {
                let tgt_node = match src.span {
                    Some(span) => DepNode::Local(src.src_id, span),
                    None => DepNode::External(src.src_id),
                };
                graph.insert_edge(src_node, tgt_node)
            }
        }
        trace!("Graph:\n{}", graph);

        // We need to compute the reachability graph. An easy way is simply
        // to use Dijkstra on every external definition which triggered an
        // error.
        for id in &self.external_decls_with_errors {
            let reachable = dijkstra(&graph.dgraph, DepNode::External(*id), None, &mut |_| 1);
            trace!("id: {:?}\nreachable:\n{:?}", id, reachable);

            let reachable: Vec<rustc_span::Span> = reachable
                .iter()
                .filter_map(|(n, _)| match n {
                    DepNode::External(_) => None,
                    DepNode::Local(_, span) => Some(span.rust_span()),
                })
                .collect();

            // Display the error message
            let span = MultiSpan::from_spans(reachable);
            let msg = format!(
                "The external definition `{}` triggered errors. \
                It is (transitively) used at the following location(s):",
                f.format_object(*id)
            );
            if self.error_on_warnings {
                self.dcx.span_err(span, msg);
            } else {
                self.dcx.span_warn(span, msg);
            }
        }
    }
}
