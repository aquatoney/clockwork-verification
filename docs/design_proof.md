# Conservative domain design: semantics and completed-horizon theorem

The target here is a design property: if an executor follows the abstract rules
and binding contracts, its completed model-visible result agrees with an
independent sequential reference. A proof that C++ faithfully implements these
rules is separate. A missing definition inside the abstract model is not treated
as an implementation detail.

## State, events, and handlers

`DES.Model Value Aggregate domains` defines the event model. A natural event key
encodes a fixed timestamp/reference tie order; `timeOrdered` says increasing
keys cannot decrease time. An event has an owner in `Fin domains`, a deterministic
handler, a state-dependent successor list, and an aggregate contribution.
Handler contracts cover model-store effects. Successor generation and aggregate
contributions depend only on the handler's declared reads (`emitLocal` and
`contributionLocal`). A successor has a strictly later reference key; equal
simulation timestamps remain possible with a later tie key. Remote successors
also obey the declared lookahead lower bound.

An event key identifies a resolved event/handler specification. Pending events
are a multiplicity function, so repeated occurrences of a key are counted rather
than silently deduplicated. An instantiation whose tie policy distinguishes
those occurrences must assign distinct keys accordingly. Event keys/timestamps
cannot be chosen retroactively from a desired execution order.

`DES.State` consists of:

- The model store.
- The pending-event multiset, including events in both queues and transport.
- The aggregate value under the declared identity/associative/commutative algebra.

`fire model event state` has fixed semantics: consume one occurrence of the
selected event, apply its handler, insert exactly the successors returned by
`emit event state.store`, and merge the returned contribution into the aggregate.
There is no arbitrary post-handler materialization callback. The store update,
successor list, and contribution are the joint effects of the same invocation,
evaluated from its pre-event store.

`fire_pending_balance` proves one-step consumption/production accounting.
`composed_event_accounting` derives finite-run multiplicity balance:

```text
final pending + consumed occurrences = initial pending + generated occurrences
```

The lists in its proof are accumulated from the actual fired-event labels and
their actual successor outputs. Consumption is permitted only for a present
event. Transport is abstracted by erasing location; it cannot erase an event from
this global pending multiset. The earlier concrete routing lemmas support this
projection, but refinement of a complete mailbox implementation is not proved.

## Independent execution relations

For a fixed observation horizon H:

- `Ready` means a pending occurrence exists and its timestamp is at most H.
- `ReferenceEnabled` selects a globally least ready reference key. It uses no
  domain clocks, compiled grouping, execution log, or composed schedule.
- `ComposedEnabled` selects a reference minimum within its own domain, and its
  timestamp must lie within a conservative domain safe bound.
- `DomainEnabled` uses the actual domain admission `Bound`, evaluated with H as
  the active window and the certified safe time. Successful compilation forces
  this field to `.effective`, hence numeric `min(H, safe)`.

`Run` is a finite inductive execution relation. It repeatedly invokes `fire` and
therefore generates events dynamically in each run. The reference does not sort
and replay the event set produced by the composed run.

`Complete model H state` means that **every pending event with timestamp at or
before H has zero multiplicity**. This includes all newly generated successors.
Future events remain pending and are part of the observation being compared.
Completion is not fuel exhaustion, an empty current batch, or a published clock.

## Local conservative clock contracts

A `ClockCertificate` supplies completed frontiers and safe bounds satisfying:

1. Every pending event is strictly later than its owner's completed frontier.
2. Each safe bound is no earlier than its own completed frontier.
3. Each receiver's safe bound is at most each other sender's frontier plus that
   sender-to-receiver lookahead.

Frontiers use integers to allow a completed frontier before time zero. Safe
times and event timestamps remain natural numbers. The model represents a
delay bound for each pair of different domains; a missing communication edge can
be assigned any conservative bound because its emission premise is empty.

Certificates may change at each composed step; there is no fixed preselected
round partition or global ordering of calls. They are local completed-frontier
and lookahead facts, rather than a hypothesis that the desired execution trace
is already ordered. A concrete protocol must furnish truthful certificates.
This artifact does not prove its progress or its implementation.

`certificate_after` proves that firing any pending event preserves a given
certificate's closed-frontier property. `incoming_later` derives that a remote
successor generated by a pending producer cannot precede work admitted through
the receiver's safe bound. Thus later materialization of successors cannot
invalidate the selected event's local minimum in the reordering argument.

## Proof and compiler connection

`DomainIndependent` says that handlers from distinct domains have compatible
ordinary model effects. It is derived by `compiled_domain_independent` from the
accepted domain's checked summaries, together with `Within` coverage of actual
handler reads/writes by their owner's summary. Aggregate effects are handled
separately by the associative/commutative reduction algebra.

The main proof is a finite execution argument:

1. `fire_commutes` proves that two distinct, present, compatible events commute
   in the **entire** state. Read locality makes their successor lists and
   contributions stable under the other handler; pending counts and the
   aggregate are proved equal, not omitted from the comparison.
2. `mixed_diamond` compares a composed choice with an independently selected
   global reference minimum. If the event keys differ, local minimum order
   proves they belong to different domains. Compiled summary compatibility
   provides store independence. Conservative clock and lookahead facts keep
   both steps legal after exchanging them.
3. `extract_reference` moves that reference event through an actual completed
   composed execution, removing exactly one processing step.
4. `completed_run_reference` repeats extraction. It constructs a reference run
   with the same step count and the exact same final state. No reference run
   with a matching result is assumed.
5. `reference_unique` proves that any two completed reference runs from the same
   initial state have equal results. `compiled_completed_observations` exposes
   equality of store, aggregate value, and pending multiplicities explicitly.

`compiled_domain_design_reference` begins with actual Core compilation and a
recursive domain occurrence in its output. The compiler provides effective
admission, compatible summaries, and a valid ownership plan. `ProgramBinding`
provides the event model's relationship to that domain:

- Each event node is known, and its abstract owner agrees with `locateOwner` in
  the compiled plan; domain counts agree.
- The local body is a `SequentialDispatcher`: sequential handler dispatch with
  optional drain preludes.
- Every event handler belongs to the body's declared handler types.
- Handler effects are covered by the corresponding checked domain summary.

The theorem constructs the completed reference run and also returns the checked
ownership fact and owner lookup correspondence. The DSL corollary starts at
`compileProgram` and uses `program.horizon`, with horizon preservation proved by
the existing DSL pipeline theorem. These are contracts for the abstract event
dispatch design; they are not a mechanized translation of the separate fuelled
interpreter's action-instance interface.

## Witness and rejected step

`DESExamples.lean` instantiates a two-domain accepted Core program and DSL
Partition/Sequential program. Event 1 runs before event 0. Depending on local
state, event 1 generates event 3 in its own domain and a future event 4 in the
other domain. After the earlier event is processed, a fresh frontier certificate
admits event 3. Horizon 4 completes with aggregate 7 and event 4 still pending.

The file independently constructs the global reference order 0, 1, 3, checking
its enabling rules and final state. It invokes the general theorem and the
compiler/DSL corollaries. Replacing lookahead 2 with lookahead 0 makes the
proposed first late-event admission impossible; this is proved from the local
clock inequalities, not from an assumed global trace order.

## Exact remaining design boundary

This result proves the completed-horizon observation criterion for a **static
Partition with local reference-order event dispatch**, under the stated abstract
binding and conservative clock contracts. It covers dynamic successor generation
and global pending-event multiplicities. It does not require an implementation
proof, nor assume the final observation equality as a contract.

It does not prove termination: a finite composed run completing H is a premise.
Given that run, existence of a corresponding completed reference run is a
conclusion. Deadlock freedom, fairness, clock publication progress, and absence
of infinite same-time generation are separate liveness questions.

The reduction observation is the declared aggregate algebra. The existing
`three_level_reduction`, concrete fold lemmas, and `hierarchical_observation`
prove grouping identities for supplied contributions. The artifact does not
provide a single refinement theorem relating every generated contribution to
all buffers of the separate IR interpreter.

The new theorem does **not** establish a general refinement from recursive
`Execution.evaluate` to `DES.Run`. Arbitrary Batch grouping, stateful Filter and
Choice effects, nested/dynamic domain changes, and full Stage-program observation
equivalence are not established by this theorem. Their existing structural,
local commutation, admission, ownership, and reduction results remain useful
separate facts. Extending completed-horizon equivalence to those constructs is
a remaining abstract-design proof task, distinct from verifying C++ faithfulness.
