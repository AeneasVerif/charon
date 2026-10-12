# Structured Control-Flow

We obtain from `rustc` function bodies that have unstructured control-flow
(see [the chapter explaining the difference][output-choices]).
We reconstruct structured control-flow ourselves by analyzing the control-flow graph.

`rustc`'s MIR records no information about the original loops/`if`s/`match`s or even blocks, so we
only have the control-flow graph to start from.
For that reason, the resulting structured control-flow may look different from the original Rust code.
It will be semantically equivalent however.

We detect loops by identifying backedges in a postorder traversal of the graph, and based on that we
need two more things: loop exits (which are where a `break` out of the loop will be), and switch
exits (where the arms of a `if`/`match` join back together). We detect these using heuristics.
These heuristics don't affect correctness, only how pretty the output looks.

By default we sometimes [duplicate code][duplication] to make the output legible. To avoid that, you may pass
`--no-code-duplication`. This changes reconstruction to instead use an algorithm based on the
[Beyond Relooper](https://dl.acm.org/doi/10.1145/3547621) paper, which guarantees no duplication by
using `loop { if foo() { break }; ...; break }` to get "forward jumps".

[output-choices]: ../output-choices/control-flow.md
[duplication]: ../output-choices/control-flow.md#code-duplication
