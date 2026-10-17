# Clockwork Verification

Lean 4 formalization accompanying **Clockwork: A Compiler for Composable Network
Simulation Schedulers** (ACM SIGOPS ATC 2026, Section 4.2).

The artifact contains a recursive DSL and IR compiler, executable finite IR
semantics, and theorems connecting successful compilation to those semantics.
It distinguishes compiler-established obligations, consequences under explicit
binding/runtime contracts, and the correspondence to the C++ implementation.

## Reproduce

Install the toolchain pinned by `lean-toolchain` (`leanprover/lean4:v4.8.0`), then
run from this repository:

```sh
lake build
python3 scripts/check.py
```

The second command also builds and audits the principal theorems' printed axiom
dependencies. It can be used alone. Lean 4.8.0 and its bundled libraries suffice;
there are no external Lean packages. Python 3 is used only by the audit script.
All proof files and executable examples belong to the default build. CI runs
the same audit. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed;
proof placeholders and custom axioms are rejected.

## What is proved

All names below are in namespace `Clockwork.Core`.

**Compiler obligations.** `pipeline_sound` and `dsl_pipeline_sound` establish the
five IR obligations for every accepted Core/DSL program. The latter also
preserves the program horizon. `accepted_normal_form` proves that normalizing
accepted output again changes nothing.

| Paper condition | IR predicate | Meaning |
|---|---|---|
| I1, IR part | `Bounded`, `EntryLegal` | Domain admission and spatial drains use their lexical effective bound; outer stream entries have been resolved. |
| I2, IR part | `Reduced` | Batch reductions in domains include partition folds and the required barrier/global-fold epilogue. |
| I3, IR part | `Ordered` | Each domain boundary routes before announcing its effective bound. |
| I4, declared facts | `RaceFree` | Declared parallel groups and cross-domain summaries have compatible effects. |
| I5, declared facts | `Conserved` | Each modeled node has exactly one owner in each resolved plan, with no unknown owned nodes. |

The transformations establish I1–I3's structural conditions; validation checks
declared effects and resolved ownership. This is not a proof that arbitrary
external handler code agrees with a declaration.

**Recursive IR execution.** `Execution.lean` defines `evaluate`, a fuel-bounded
interpreter for recursive `Code`: sequencing, loops, state-dependent branches,
domain visits, admission, handlers, transforms, reductions, routing,
announcements, epilogues, and resolved plan changes. The scheduling state has
model storage, queues, admitted buffers, reduction buffers/results, plans,
outgoing/delivered events, frontiers, and synchronization signals.

`compiled_execution_reference` and `dsl_execution_reference` prove that an
accepted program has the same interpreter result when each parallel call is
executed in its requested order or in sorted reference-priority order. The
comparison preserves the order of different calls and all other IR operations.
It covers the interpreter's entire state, including queues and reduction values,
and is parameterized by the same binding/runtime in both executions. This is
**serialization within each checked parallel call**, not an unconditional
comparison with a globally timestamp-sorted DES simulator.

The proof derives independence from `pipeline_sound` and a binding realization
contract, then invokes `reference_equivalence`; it does not assume
`ConflictOrdered` for compiled output. Runtime action lists must be permutations
of the declared occurrences, preserving multiplicities. Sequential calls must
retain their declared access order. Actual handlers carry proofs of frame and
locality. See [the semantic specification](docs/semantics.md) for these inputs.

**Reference order across calls.** `evaluate_calls_safe` establishes safety for
every parallel call in an actual finite semantic execution. The theorem
`compiled_handler_trace_reference` derives reference-trace equivalence from
successful compilation and that execution, given two additional runtime order
conditions: sequential calls are priority-sorted, and different calls occupy
ordered reference-priority bands (`CallsChronological`). This is a sufficient,
explicitly stronger cross-call condition; compilation does not prove it. The
result concerns the handler subtrace, not erasure of transform/reduction effects.
Within a parallel call, priorities can be inverted because independence is
proved from compiler checks. No `ConflictOrdered` hypothesis is supplied to this
theorem. The more general conditional trace theorem remains available in
`Trace.lean`.

**Operational consequences of the other obligations.** These are tied to the
same queue, boundary, and fold operations used by the interpreter:

| Theorem | Consequence and additional assumptions |
|---|---|
| `compiled_drain_safe`, `compiled_admit_safe` | Spatial admission uses numeric `min(window, safe)`; admitted work respects safe time. Already admitted work must also be within the current bound. |
| `compiled_admission_no_unseen_predecessor` | No unseen event from a specified incoming edge precedes admitted work, under that edge's closed completed-frontier and lookahead contracts. Availability is not simply assumed. |
| `admit_conserves_events` | Admission preserves multiplicity across queued and admitted buffers, including repeated drains. |
| `compiled_domain_contract`, `compiled_boundary_signals` | A compiled domain has its required epilogue and concretely routes before announcing the numeric effective bound. |
| `compiled_boundary_conserves_outputs` | The boundary preserves every outgoing event in the delivered buffer. |
| `compiled_domain_has_owner` | Each known model node has an owner in the compiled domain plan. |
| `batchFold_preserves_aggregate`, `partitionFold_preserves_aggregate`, `globalFold_matches_grouped_fold` | Concrete fold operations implement the stated reduction algebra. `three_level_reduction` supplies the batch/partition/global algebraic identity. |

Clock monotonicity and completion are not manufactured by boundary normalization:
`announcement_monotone` explicitly requires a forward frontier. Earliest-event
bounds with inclusive endpoints require the separate FIFO/tie-order contract in
`fifo_endpoint_safe`, rather than the closed-frontier premise above.

## Executable witnesses and scope checks

`Examples.lean` includes a nonempty accepted execution with two domains, an
actually inverted independent pair, tightened admission, a retained future
event, routing, announcements, and a global aggregate. It invokes the compiler
execution theorem and the compiler-to-handler-trace theorem with concrete order
certificates. DSL execution, finite loop unfolding, branching, and fuel
exhaustion are also exercised. Acceptance checks still reject conflicting
parallel groups and overlapping ownership.

The examples also check two limits: a singleton declaration cannot realize two
conflicting occurrences, and two individually safe calls can violate global
reference order. These witnesses prevent the cross-call runtime contract from
being mistaken for a compiler-established property.

## Files

| File | Purpose |
|---|---|
| `Clockwork.lean` | Queue, reduction, and reordering foundations; historical flat sync illustration. |
| `Core.lean` | Recursive IR, passes, validation, pipeline soundness, normalization stability. |
| `DSL.lean` | Surface stages, lowering, DSL compilation, acceptance/rejection/repair examples. |
| `Semantics.lean` | Handler contracts, lookahead and endpoint lemmas, ownership, routing, admission commutation. |
| `Trace.lean` | Priority reference ordering and conditional trace equivalence. |
| `Bridge.lean` | Occurrence-preserving permutations and compiler-to-local-execution bridges. |
| `Execution.lean` | Recursive executable semantics and compiler/DSL semantic refinement. |
| `ExecutionTrace.lean` | Safety of dynamically recorded calls and conditional global handler-trace equivalence. |
| `ExecutionObligations.lean` | Admission, boundary, ownership, and fold consequences in the interpreter state. |
| `Examples.lean` | Nonempty execution witnesses and counterexamples to stronger claims. |

`normalizeSync` is a historical flat illustration. The compiler and new execution
proofs use recursive `Code`, `syncPass`, and `fixBoundary`.

## Connection to the implementation and proof boundary

The original source comparison used Clockwork commit
`db1da12e2c00e3e92e06e339c0084071d8c8de5c`, notably
`include/clockwork/dsl/strategy_program.h` and `src/ir/pass/`. The model represents
resolved, lexical bounds and plans; SSA resolution, dynamic binding discovery,
and generated C++ code must implement those contracts.

This artifact does **not** include a mechanized translation of C++, a concurrent
message-passing runtime, a termination/progress proof, or an independently
event-generating reference DES simulator. Domain visits in `evaluate` are serial;
the artifact does not derive arbitrary cross-domain interleaving safety from
declared domain summaries. Such summaries must cover actual effects under the
binding contract. Event generation and external callable behavior are supplied
by the deterministic runtime interface. Their faithfulness to C++ is not checked
by Lean. Program horizon is preserved as metadata; reaching a completed horizon
is an execution obligation.

Passes repair potentially unsafe input IR. We prove properties and semantic
serialization of accepted **output**, not equality with the behavior of unsafe
pre-normalization IR. The full paper-level completed-horizon observation
criterion additionally relies on binding validity, event generation/delivery,
round completion, and implementation correspondence. The exact formal scope and
remaining contracts are specified in [docs/semantics.md](docs/semantics.md).

## Development assistance

The initial formalization was developed with assistance from Kimi K3. The
subsequent execution semantics, compiler bridges, examples, and proof-scope
review were developed with assistance from OpenAI Codex. Authors are responsible
for reviewing the definitions, theorem statements, and implementation contracts;
a successful Lean build checks the formal derivations, not correspondence to
the intended system by itself.

## License

MIT; see [LICENSE](LICENSE).
