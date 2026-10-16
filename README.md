# Clockwork Verification

Lean 4 formalization of the conservative scheduling core of Clockwork,
accompanying the paper "Clockwork: A Compiler for Composable Network
Simulation Schedulers" (ACM SIGOPS ATC 2026, Section 4.2).

The Lean model covers the conservative scheduling core described in Section 4.2.
It defines a recursive DSL, lowering, four IR transformations, executable checks,
and the resulting IR obligations. Separate execution lemmas connect these
obligations to queue conservation, dependency safety, reductions, and reference
trace order.

## Reproduce

Install the Lean version pinned by `lean-toolchain`
(`leanprover/lean4:v4.8.0`), then run:

```sh
lake build
```

Lean 4.8.0 and its bundled libraries are sufficient. No external proof packages
are required. The build checks every theorem and the concrete acceptance,
rejection, and pass-repair examples in `DSL.lean`. Principal theorems print their
axiom dependencies; these contain only Lean's standard logical axioms.

## Main Results

`DSL.dsl_pipeline_sound` preserves the program horizon and proves all five IR
obligations for every program accepted by the modeled compiler.
`Core.pipeline_sound` proves the corresponding result over recursive core IR.
The validator checks declared effects and ownership; the proof of bound,
boundary, and reduction placement comes from the transformations themselves.
`Core.accepted_normal_form` proves that a second normalization leaves accepted
IR unchanged.

| Paper condition | Formal predicate | Meaning |
|---|---|---|
| I1, IR part | `Bounded` and `EntryLegal` | Spatial admission and local drains use the enclosing effective bound; outer stream entries have been resolved. |
| I2, IR part | `Reduced` | Global batch accumulators have a partition fold and the enclosing domain has the required barrier/global-fold epilogue. |
| I3, IR part | `Ordered` | Each domain boundary routes before announcing its effective bound. |
| I4, declared facts | `RaceFree` | Declared parallel groups and domain summaries have compatible read/write footprints. |
| I5, declared facts | `Conserved` | Every model node has exactly one owner in each resolved domain plan; every owned node belongs to the model. |

## File Map

- `Clockwork.lean`: single-domain queue semantics and the reusable lemmas:
  drain admission and conservation, sync retargeting, the fold algebra, and
  run reordering.
- `Core.lean`: the recursive core IR, the four passes, the per-pass
  establish/preserve lemmas, `pipeline_sound`, and `accepted_normal_form`.
- `DSL.lean`: the surface DSL, its lowering, and `dsl_pipeline_sound`.
- `Semantics.lean`: the execution model: stores, handler frame conditions,
  and binding contracts.
- `Trace.lean`: the reference trace (timestamp/tie order) and trace lemmas.

## License

MIT; see `LICENSE`.
