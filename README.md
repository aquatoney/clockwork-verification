# Clockwork Verification

Lean 4 formalization accompanying **Clockwork: A Compiler for Composable Network
Simulation Schedulers** (ACM SIGOPS ATC 2026, Section 4.2).

The artifact contains a recursive DSL and IR compiler, executable finite IR
semantics, and theorems connecting successful compilation to those semantics.
A second event-generating design model proves completed-horizon equivalence
for the static-domain conservative scheduling core. These are abstract-design
results; correspondence to the C++ implementation is a separate obligation.

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

**Event-generating DES design.** `DES.lean` defines an event step that consumes
one pending occurrence, executes the event's handler, generates successors from
the pre-event state, and accumulates the event contribution. The global pending
multiset includes queued and in-flight events. Composed execution chooses a
local reference minimum through its conservative safe bound; sequential
reference execution independently chooses a global reference minimum. Each run
generates its own successors. There is no opaque `commit` in this model.

`DES.completed_run_reference` constructs a complete sequential reference run
from any finite composed run that has completed horizon H. Model storage,
aggregate value, and the entire pending multiset are identical. It does not
assume `ConflictOrdered`, `CallsChronological`, a common precomputed event log,
or the existence of a reference run with the desired answer.

`DES.compiled_domain_design_reference` connects that design result to an
accepted domain's effective bound, checked domain summaries, and resolved plan.
`DES.dsl_domain_design_reference` starts from DSL compilation and uses the
program horizon. `ProgramBinding` explicitly restricts the local body to a
sequential dispatcher (with optional drain preludes), associates event handlers
with its declared handler types, and maps event nodes to the compiled plan.
The compiler establishes summary compatibility; the binding establishes that
those summaries cover the actual abstract handlers.

This theorem covers **static domains with local reference-order dispatch**.
It does not prove a refinement from the complete recursive IR interpreter to
the event-generating model. Arbitrary Batch event grouping, Filter/Choice state
effects, and dynamic repartitioning are not covered by this completed-horizon
theorem. Their structural and local-operation results remain separate below.
These are remaining **design proof** boundaries, distinct from C++ faithfulness.

A clock certificate states local completed frontiers, forward safe bounds, and
lookahead inequalities. It may change at every event step. The proof derives
the safe reordering of a domain choice and the reference minimum from these
conditions and checked effects; whole-execution ordering is not supplied as a
hypothesis. Completion means no pending event at or before H, not exhaustion
of an interpreter's fuel. No unconditional termination or clock-progress theorem
is claimed. See [the design specification and proof map](docs/design_proof.md).

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

`DESExamples.lean` checks a late-first domain execution with state-dependent
successor generation, a separately executed global reference schedule, an
identical aggregate, and a retained future event. It invokes both Core and DSL
design bridges. A negative example checks that insufficient lookahead prevents
the proposed late-first step.

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
| `Examples.lean` | Structured-interpreter witnesses and counterexamples. |
| `DES.lean` | Event-generating semantics, local conservative clock contracts, reference-run construction, and static-domain compiler/DSL bridges. |
| `DESExamples.lean` | Independently generated reference/composed executions, dynamic successors, and lookahead rejection. |

`normalizeSync` is a historical flat illustration. The compiler and new execution
proofs use recursive `Code`, `syncPass`, and `fixBoundary`.

## Connection to the implementation and proof boundary

The original source comparison used Clockwork commit
`db1da12e2c00e3e92e06e339c0084071d8c8de5c`, notably
`include/clockwork/dsl/strategy_program.h` and `src/ir/pass/`. The model represents
resolved, lexical bounds and plans; SSA resolution, dynamic binding discovery,
and generated C++ code must implement those contracts.

The design model, structured IR interpreter, and C++ implementation are three
different objects. `DES.lean` proves completed-horizon equivalence for its
specified static-domain design. `Execution.lean` proves group serialization in
the structured IR interpreter. A general refinement from that interpreter,
including arbitrary Stage composition, to the DES model is **not** proved.
The executable design example and `ProgramBinding` make the covered fragment
explicit; the presence of two models is not itself a proof of their general
correspondence.

No mechanized C++ translation, concrete transport protocol, termination guarantee,
or clock-progress proof is included. Implementations must realize the abstract
handler, ownership, and completed-frontier contracts. In the DES model, transport
location is erased while every queued/in-flight event remains in the global
pending multiset. The correctness proof is conditional on reaching a completed
horizon; it constructs a corresponding completed sequential run rather than
assuming one.

Passes repair potentially unsafe input IR. We prove properties of accepted
output, not preservation of unsafe pre-normalization behavior. The exact
separation between the [design theorem](docs/design_proof.md), the
[structured interpreter](docs/semantics.md), and implementation correspondence
is part of the artifact's specification.

## Development assistance

This artifact was developed with assistance from AI coding agents, including
Kimi K3. The authors are responsible for reviewing the definitions, theorem
statements, and implementation contracts; a successful Lean build checks the
formal derivations, not correspondence to the intended system by itself.

## License

MIT; see [LICENSE](LICENSE).
