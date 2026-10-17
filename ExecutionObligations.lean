import ExecutionTrace

namespace Clockwork.Core

theorem allThrough_append (bound : Nat) (before after : List Clockwork.Event)
    (first : Clockwork.allThrough bound before) (second : Clockwork.allThrough bound after) :
    Clockwork.allThrough bound (before ++ after) := by
  induction before with
  | nil => exact second
  | cons event rest ih => exact ⟨first.1, ih first.2⟩

theorem occurrences_append (target : Clockwork.Event) (before after : List Clockwork.Event) :
    Clockwork.occurrences target (before ++ after) =
      Clockwork.occurrences target before + Clockwork.occurrences target after := by
  induction before with
  | nil => simp [Clockwork.occurrences]
  | cons event rest ih =>
    change (if event = target then 1 else 0) + Clockwork.occurrences target (rest ++ after) =
      ((if event = target then 1 else 0) + Clockwork.occurrences target rest) +
        Clockwork.occurrences target after
    rw [ih]
    omega

theorem compiled_admit_safe (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (bound : Bound)
    (site : List.Mem (true, bound) (admissionSites false output))
    (ctx : Context) (state : Machine Value)
    (prior : Clockwork.allThrough ctx.safe (state.admitted ctx.owner)) :
    Clockwork.allThrough ctx.safe ((admitQueue ctx bound state).admitted ctx.owner) := by
  simp only [admitQueue, update_here]
  exact allThrough_append _ _ _ prior
    (compiled_drain_safe nodes input output accepted bound site ctx.window ctx.safe (state.queues ctx.owner))

-- Includes an already admitted buffer: repeated admission cannot erase events.
theorem admit_conserves_events (ctx : Context) (bound : Bound) (state : Machine Value)
    (event : Clockwork.Event) :
    Clockwork.occurrences event ((admitQueue ctx bound state).admitted ctx.owner) +
      Clockwork.occurrences event ((admitQueue ctx bound state).queues ctx.owner) =
      Clockwork.occurrences event (state.admitted ctx.owner) +
        Clockwork.occurrences event (state.queues ctx.owner) := by
  simp only [admitQueue, update_here]
  rw [occurrences_append]
  have conserved := Clockwork.drain_conservation
    (evalBound ctx.window ctx.safe bound) (state.queues ctx.owner) event
  omega

theorem compiled_boundary_signals (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (p e w body boundary tail)
    (site : Subcode (.domain p e w body boundary tail) output)
    (ctx : Context) (state : Machine Value) :
    (executeBoundary ctx boundary state).signals = state.signals ++
      [.route ctx.owner, .announce ctx.owner (Clockwork.effective ctx.window ctx.safe)] := by
  rw [(compiled_domain_contract nodes input output accepted p e w body boundary tail site).1]
  simp [executeBoundary, announce, routeOutputs, evalBound, List.append_assoc]

theorem compiled_boundary_conserves_outputs (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (p e w body boundary tail)
    (site : Subcode (.domain p e w body boundary tail) output)
    (ctx : Context) (state : Machine Value) :
    ((executeBoundary ctx boundary state).delivered).map Prod.snd =
      state.delivered.map Prod.snd ++ state.outgoing := by
  rw [(compiled_domain_contract nodes input output accepted p e w body boundary tail site).1]
  simp only [executeBoundary, announce, routeOutputs]
  rw [List.map_append, routing_conserves_events]

theorem compiled_domain_has_owner (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (p e w body boundary tail)
    (site : Subcode (.domain p e w body boundary tail) output)
    (node : Nat) (known : List.Mem node nodes) :
    exists owner, locateOwner node p = some owner :=
  owners_have_owner nodes p
    (compiled_domain_contract nodes input output accepted p e w body boundary tail site).2.2 node known

theorem partitionFold_preserves_aggregate (algebra : Clockwork.Reduction Value)
    (ctx : Context) (region : Nat) (state : Machine Value) :
    Clockwork.fold algebra ((partitionFold algebra ctx region state).partials ctx.owner region) =
      Clockwork.fold algebra (state.partials ctx.owner region) := by
  simp [partitionFold, update, Clockwork.fold, algebra.rightIdentity]

theorem batchFold_preserves_aggregate (algebra : Clockwork.Reduction Value)
    (ctx : Context) (region : Nat) (state : Machine Value) :
    Clockwork.fold algebra ((batchFold algebra ctx region state).partials ctx.owner region) =
      algebra.merge (Clockwork.fold algebra (state.partials ctx.owner region))
        (Clockwork.fold algebra (state.batchValues ctx.owner region)) := by
  simp [batchFold, update, Clockwork.fold_append, Clockwork.fold, algebra.rightIdentity]

theorem globalFold_matches_grouped_fold (algebra : Clockwork.Reduction Value)
    (ctx : Context) (region : Nat) (state : Machine Value) :
    (globalFold algebra ctx region state).totals region =
      Clockwork.fold algebra
        (ctx.domains.map (fun owner => Clockwork.fold algebra (state.partials owner region))) := by
  simp only [globalFold, update_here]
  rw [<- Clockwork.fold_groups algebra]
  simp only [List.map_map]
  rfl

-- Ordered IR fixes operation order; a nondecreasing clock additionally needs
-- a completed/forward frontier from the runtime, stated here explicitly.
theorem announcement_monotone (ctx : Context) (bound : Bound) (state : Machine Value)
    (forward : state.frontiers ctx.owner <= evalBound ctx.window ctx.safe bound) :
    state.frontiers ctx.owner <= (announce ctx bound state).frontiers ctx.owner := by
  simpa [announce, update] using forward

#print axioms compiled_admit_safe
#print axioms admit_conserves_events
#print axioms compiled_boundary_signals
#print axioms compiled_boundary_conserves_outputs
#print axioms compiled_domain_has_owner
#print axioms batchFold_preserves_aggregate
#print axioms globalFold_matches_grouped_fold

end Clockwork.Core
