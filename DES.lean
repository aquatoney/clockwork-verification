import ExecutionObligations

namespace Clockwork.Core.DES

-- Design-level semantics: an event invocation consumes one pending occurrence,
-- changes model storage, emits successor events, and contributes to an aggregate.
-- Pending includes queued AND in-flight events. Transport changes location, not
-- this global multiset. Event keys encode a fixed timestamp/reference tie order.
structure Model (Value Aggregate : Type) (domains : Nat) where
  time : Nat -> Nat
  owner : Nat -> Fin domains
  handler : Nat -> Handler Value
  emit : Nat -> Store Value -> List Nat
  contribution : Nat -> Store Value -> Aggregate
  algebra : Clockwork.Reduction Aggregate
  timeOrdered : forall a b, a <= b -> time a <= time b
  successorsLater : forall event state next, List.Mem next (emit event state) -> event < next
  emitLocal : forall event before after,
    (forall key, List.Mem key (handler event).access.reads -> before key = after key) ->
    emit event before = emit event after
  contributionLocal : forall event before after,
    (forall key, List.Mem key (handler event).access.reads -> before key = after key) ->
    contribution event before = contribution event after
  lookahead : Fin domains -> Fin domains -> Nat
  delay : forall event state next, List.Mem next (emit event state) ->
    owner event ≠ owner next ->
    time event + lookahead (owner event) (owner next) <= time next

structure State (Value Aggregate : Type) where
  store : Store Value
  pending : Nat -> Nat
  aggregate : Aggregate

def fire (model : Model Value Aggregate domains) (event : Nat)
    (state : State Value Aggregate) : State Value Aggregate :=
  { store := (model.handler event).step state.store,
    pending := fun next => state.pending next - (if next = event then 1 else 0) +
      countNode next (model.emit event state.store),
    aggregate := model.algebra.merge state.aggregate (model.contribution event state.store) }

def Ready (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) (event : Nat) : Prop :=
  0 < state.pending event /\ model.time event <= horizon

def Complete (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) : Prop :=
  forall event, model.time event <= horizon -> state.pending event = 0

-- Local conservative clock certificate. It describes completed frontiers,
-- forward safe bounds, and lookahead edges, not a desired whole-trace ordering.
-- A fresh certificate may be chosen at every step as domains advance.
structure ClockCertificate (model : Model Value Aggregate domains)
    (state : State Value Aggregate) where
  frontier : Fin domains -> Int
  safe : Fin domains -> Nat
  closed : forall event, 0 < state.pending event -> frontier (model.owner event) < (model.time event : Int)
  forward : forall owner, frontier owner <= (safe owner : Int)
  incoming : forall sender receiver, sender ≠ receiver ->
    (safe receiver : Int) <= frontier sender + (model.lookahead sender receiver : Int)

def LocalMinimum (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) (event : Nat) : Prop :=
  forall other, Ready model horizon state other -> model.owner other = model.owner event -> event <= other

def ComposedEnabled (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) (event : Nat) : Prop :=
  Ready model horizon state event /\ LocalMinimum model horizon state event /\
    exists certificate : ClockCertificate model state, model.time event <= certificate.safe (model.owner event)

-- Independent reference specification: select a globally least ready event.
-- It does not consult domain safe times, groups, certificates, or a composed log.
def ReferenceEnabled (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) (event : Nat) : Prop :=
  Ready model horizon state event /\ forall other, Ready model horizon state other -> event <= other

inductive Run (enabled : State Value Aggregate -> Nat -> Prop)
    (model : Model Value Aggregate domains) : Nat -> State Value Aggregate -> State Value Aggregate -> Prop
  | done (state) : Run enabled model 0 state state
  | step {state final event count} : enabled state event ->
      Run enabled model count (fire model event state) final -> Run enabled model (count + 1) state final

abbrev ComposedRun (model : Model Value Aggregate domains) (horizon : Nat) :=
  Run (ComposedEnabled model horizon) model

abbrev ReferenceRun (model : Model Value Aggregate domains) (horizon : Nat) :=
  Run (ReferenceEnabled model horizon) model

theorem fire_pending_balance (model : Model Value Aggregate domains) (state : State Value Aggregate)
    (event : Nat) (present : 0 < state.pending event) (next : Nat) :
    (fire model event state).pending next + (if next = event then 1 else 0) =
      state.pending next + countNode next (model.emit event state.store) := by
  simp only [fire]
  by_cases same : next = event
  · subst next; simp only [ite_true]; omega
  · simp [same]

-- Exact finite-run event accounting, including generated successors. This is
-- an equality of multiplicities, not an assumption on materialization code.
theorem composed_event_accounting (model : Model Value Aggregate domains) (horizon count : Nat)
    (initial final : State Value Aggregate) (run : ComposedRun model horizon count initial final) :
    exists consumed generated : List Nat, consumed.length = count /\
      forall event, final.pending event + countNode event consumed =
        initial.pending event + countNode event generated := by
  induction run with
  | done state => exact ⟨[], [], rfl, fun event => rfl⟩
  | @step state final event count enabled _ ih =>
    obtain ⟨consumed, generated, length, balance⟩ := ih
    refine ⟨event :: consumed, model.emit event state.store ++ generated, by simp [length], ?_⟩
    intro next
    have first := fire_pending_balance model state event enabled.1.1 next
    have rest := balance next
    rw [countNode_append]
    simp only [countNode]
    by_cases same : event = next
    · subst next
      simp only [ite_true] at *
      omega
    · have opposite : next ≠ event := Ne.symm same
      simp only [if_neg same, if_neg opposite] at *
      omega

theorem time_strict_key (model : Model Value Aggregate domains) (a b : Nat)
    (before : model.time a < model.time b) : a < b := by
  by_cases ordered : a < b
  · exact ordered
  · have time := model.timeOrdered b a (by omega)
    omega

theorem pending_survives (model : Model Value Aggregate domains) (state : State Value Aggregate)
    (event other : Nat) (different : other ≠ event) (present : 0 < state.pending other) :
    0 < (fire model event state).pending other := by
  simp only [fire, if_neg different, Nat.sub_zero]
  omega

def certificate_after (model : Model Value Aggregate domains) (state : State Value Aggregate)
    (event : Nat) (ready : 0 < state.pending event) (certificate : ClockCertificate model state) :
    ClockCertificate model (fire model event state) := by
  refine { frontier := certificate.frontier, safe := certificate.safe,
           forward := certificate.forward, incoming := certificate.incoming, closed := ?_ }
  intro next present
  by_cases prior : 0 < state.pending next
  · exact certificate.closed next prior
  · have emitted : List.Mem next (model.emit event state.store) := by
      by_cases member : List.Mem next (model.emit event state.store)
      · exact member
      · have zero := countNode_zero_of_absent next (model.emit event state.store) member
        simp only [fire] at present
        omega
    by_cases same : model.owner event = model.owner next
    · have source := certificate.closed event ready
      have later := model.timeOrdered event next (Nat.le_of_lt (model.successorsLater event state.store next emitted))
      rw [same] at source
      omega
    · have source := certificate.closed event ready
      have incoming := certificate.incoming (model.owner event) (model.owner next) same
      have forward := certificate.forward (model.owner next)
      have delay := model.delay event state.store next emitted same
      omega

theorem incoming_later (model : Model Value Aggregate domains) (state : State Value Aggregate)
    (selected producer : Nat) (certificate : ClockCertificate model state)
    (bounded : model.time selected <= certificate.safe (model.owner selected))
    (present : 0 < state.pending producer)
    (different : model.owner producer ≠ model.owner selected)
    (next : Nat) (emitted : List.Mem next (model.emit producer state.store))
    (destination : model.owner next = model.owner selected) : selected < next := by
  have source := certificate.closed producer present
  have bound := certificate.incoming (model.owner producer) (model.owner selected) different
  have other : model.owner producer ≠ model.owner next := by rw [destination]; exact different
  have delay := model.delay producer state.store next emitted other
  rw [destination] at delay
  exact time_strict_key model selected next (by omega)

-- Abstract effect coverage is a binding obligation, separate from C++ faithfulness.
def Within (actual summary : Access) : Prop :=
  (forall key, List.Mem key actual.reads -> List.Mem key summary.reads) /\
  (forall key, List.Mem key actual.writes -> List.Mem key summary.writes)

def accessAt : List Access -> Nat -> Access
  | [], _ => ⟨0, [], []⟩
  | head :: _, 0 => head
  | _ :: rest, index + 1 => accessAt rest index

theorem accessAt_member (rest : List Access) (index : Nat)
    (bounded : index < rest.length) : List.Mem (accessAt rest index) rest := by
  induction rest generalizing index with
  | nil => simp only [List.length_nil] at bounded; omega
  | cons first rest ih =>
    cases index with
    | zero => exact .head _
    | succ index => exact .tail _ (ih index (by simp only [List.length_cons] at bounded; omega))

theorem groupSafe_at (group : List Access) (safe : GroupSafe group)
    (a b : Nat) (ha : a < group.length) (hb : b < group.length) (different : a ≠ b) :
    Compatible (accessAt group a) (accessAt group b) := by
  induction group generalizing a b with
  | nil => simp only [List.length_nil] at ha; omega
  | cons head rest ih =>
    cases a with
    | zero =>
      cases b with
      | zero => exact False.elim (different rfl)
      | succ b => exact safe.1 _ (accessAt_member rest b (by simp only [List.length_cons] at hb; omega))
    | succ a =>
      cases b with
      | zero =>
        exact compatible_symmetric _ _
          (safe.1 _ (accessAt_member rest a (by simp only [List.length_cons] at ha; omega)))
      | succ b =>
        exact ih safe.2 a b (by simp only [List.length_cons] at ha; omega)
          (by simp only [List.length_cons] at hb; omega) (by omega)

theorem within_compatible (a b sa sb : Access) (ca : Within a sa) (cb : Within b sb)
    (safe : Compatible sa sb) : Compatible a b :=
  ⟨(fun key ha hb => safe.1 key (ca.2 key ha) (cb.2 key hb)),
   (fun key ha hb => safe.2.1 key (ca.2 key ha) (cb.1 key hb)),
   (fun key hb ha => safe.2.2 key (cb.2 key hb) (ca.1 key ha))⟩

def DomainIndependent (model : Model Value Aggregate domains) : Prop :=
  forall a b, model.owner a ≠ model.owner b ->
    Compatible (model.handler a).access (model.handler b).access

theorem raceFree_subcode {child code : Code} (site : Subcode child code) : RaceFree code -> RaceFree child := by
  induction site with
  | here => exact id
  | left _ ih | yes _ ih => exact fun h => ih h.1
  | right _ ih | no _ ih | domain _ ih | entry _ ih => exact fun h => ih h.2
  | loop _ ih => exact ih

theorem compiled_domain_independent (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (p effects w body boundary tail)
    (site : Subcode (.domain p effects w body boundary tail) output)
    (model : Model Value Aggregate effects.length)
    (coverage : forall event, Within (model.handler event).access
      (accessAt effects (model.owner event).val)) : DomainIndependent model := by
  have sub := raceFree_subcode site (pipeline_sound nodes input output accepted).i4
  intro a b different
  apply within_compatible _ _ _ _ (coverage a) (coverage b)
  apply groupSafe_at effects sub.1 (model.owner a).val (model.owner b).val
    (model.owner a).isLt (model.owner b).isLt
  exact fun same => different (Fin.ext same)

theorem state_ext {a b : State Value Aggregate} (store : a.store = b.store)
    (pending : a.pending = b.pending) (aggregate : a.aggregate = b.aggregate) : a = b := by
  cases a; cases b; cases store; cases pending; cases aggregate; rfl

theorem fire_commutes (model : Model Value Aggregate domains) (state : State Value Aggregate)
    (a b : Nat) (ha : 0 < state.pending a) (hb : 0 < state.pending b) (different : a ≠ b)
    (compatible : Compatible (model.handler a).access (model.handler b).access) :
    fire model b (fire model a state) = fire model a (fire model b state) := by
  have readsA : forall key, List.Mem key (model.handler a).access.reads ->
      (model.handler b).step state.store key = state.store key :=
    fun key read => (model.handler b).frame state.store key (fun write => compatible.2.2 key write read)
  have readsB : forall key, List.Mem key (model.handler b).access.reads ->
      (model.handler a).step state.store key = state.store key :=
    fun key read => (model.handler a).frame state.store key (fun write => compatible.2.1 key write read)
  have emitA := model.emitLocal a ((model.handler b).step state.store) state.store readsA
  have emitB := model.emitLocal b ((model.handler a).step state.store) state.store readsB
  have valueA := model.contributionLocal a ((model.handler b).step state.store) state.store readsA
  have valueB := model.contributionLocal b ((model.handler a).step state.store) state.store readsB
  apply state_ext
  · exact compatible_handlers_commute _ _ compatible state.store
  · funext event
    simp only [fire, emitA, emitB]
    by_cases sameA : event = a
    · subst event
      simp only [ite_true, if_neg different]
      omega
    · by_cases sameB : event = b
      · subst event
        have other : b ≠ a := Ne.symm different
        simp only [ite_true, if_neg other]
        omega
      · simp only [if_neg sameA, if_neg sameB, Nat.sub_zero]
        omega
  · simp only [fire, valueA, valueB]
    rw [model.algebra.associative, model.algebra.associative,
      model.algebra.commutative (model.contribution a state.store) (model.contribution b state.store)]

theorem new_pending_emitted (model : Model Value Aggregate domains) (state : State Value Aggregate)
    (event next : Nat) (present : 0 < (fire model event state).pending next)
    (absent : ¬ 0 < state.pending next) : List.Mem next (model.emit event state.store) := by
  by_cases member : List.Mem next (model.emit event state.store)
  · exact member
  · have zero := countNode_zero_of_absent next (model.emit event state.store) member
    simp only [fire] at present
    omega

theorem reference_survives (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) (reference other : Nat)
    (first : ReferenceEnabled model horizon state reference)
    (ready : Ready model horizon state other) (different : reference ≠ other) :
    ReferenceEnabled model horizon (fire model other state) reference := by
  constructor
  · exact ⟨pending_survives model state other reference different first.1.1, first.1.2⟩
  · intro next nextReady
    by_cases present : 0 < state.pending next
    · exact first.2 next ⟨present, nextReady.2⟩
    · have emitted := new_pending_emitted model state other next nextReady.1 present
      have later := model.successorsLater other state.store next emitted
      have order := first.2 other ready
      omega

theorem composed_survives_reference (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) (selected reference : Nat)
    (chosen : ComposedEnabled model horizon state selected)
    (first : ReferenceEnabled model horizon state reference)
    (different : selected ≠ reference) :
    ComposedEnabled model horizon (fire model reference state) selected := by
  have differentOwners : model.owner reference ≠ model.owner selected := by
    intro same
    have localOrder := chosen.2.1 reference first.1 same
    have globalOrder := first.2 selected chosen.1
    exact different (by omega)
  obtain ⟨certificate, bounded⟩ := chosen.2.2
  refine ⟨⟨pending_survives model state reference selected different chosen.1.1, chosen.1.2⟩, ?_, ?_⟩
  · intro next ready sameOwner
    by_cases present : 0 < state.pending next
    · exact chosen.2.1 next ⟨present, ready.2⟩ sameOwner
    · exact Nat.le_of_lt (incoming_later model state selected reference certificate bounded first.1.1
        differentOwners next (new_pending_emitted model state reference next ready.1 present) sameOwner)
  · exact ⟨certificate_after model state reference first.1.1 certificate, bounded⟩

theorem mixed_diamond (model : Model Value Aggregate domains) (horizon : Nat)
    (independent : DomainIndependent model) (state : State Value Aggregate)
    (selected reference : Nat) (chosen : ComposedEnabled model horizon state selected)
    (first : ReferenceEnabled model horizon state reference) (different : selected ≠ reference) :
    ReferenceEnabled model horizon (fire model selected state) reference /\
    ComposedEnabled model horizon (fire model reference state) selected /\
    fire model reference (fire model selected state) = fire model selected (fire model reference state) := by
  have owners : model.owner selected ≠ model.owner reference := by
    intro same
    have localOrder := chosen.2.1 reference first.1 same.symm
    have globalOrder := first.2 selected chosen.1
    exact different (by omega)
  exact ⟨reference_survives model horizon state reference selected first chosen.1 (Ne.symm different),
    composed_survives_reference model horizon state selected reference chosen first different,
    fire_commutes model state selected reference chosen.1.1 first.1.1 different
      (independent selected reference owners)⟩

theorem complete_not_ready (model : Model Value Aggregate domains) (horizon : Nat)
    (state : State Value Aggregate) (complete : Complete model horizon state)
    (event : Nat) (ready : Ready model horizon state event) : False := by
  have zero := complete event ready.2
  have positive := ready.1
  omega

-- Pull the independently selected reference event through an actual finite
-- composed execution. Its generation and contribution move with its handler.
theorem extract_reference (model : Model Value Aggregate domains) (horizon : Nat)
    (independent : DomainIndependent model) (count : Nat) (initial final : State Value Aggregate)
    (run : ComposedRun model horizon count initial final) (complete : Complete model horizon final)
    (event : Nat) (first : ReferenceEnabled model horizon initial event) :
    exists rest, count = rest + 1 /\ ComposedRun model horizon rest (fire model event initial) final := by
  induction run with
  | done state => exact False.elim (complete_not_ready model horizon state complete event first.1)
  | @step state final selected count chosen tail ih =>
    by_cases same : selected = event
    · subst selected
      exact ⟨count, rfl, tail⟩
    · have diamond := mixed_diamond model horizon independent state selected event chosen first same
      obtain ⟨rest, length, remainder⟩ := ih complete diamond.1
      refine ⟨rest + 1, by omega, .step diamond.2.1 ?_⟩
      rw [<- diamond.2.2]
      exact remainder

theorem exists_least (predicate : Nat -> Prop) (witness : Nat) (known : predicate witness) :
    exists first, predicate first /\ forall other, predicate other -> first <= other := by
  induction witness using Nat.strongInductionOn with
  | ind witness ih =>
    letI : Decidable (exists other, other < witness /\ predicate other) := Classical.propDecidable _
    by_cases earlier : exists other, other < witness /\ predicate other
    · obtain ⟨other, before, member⟩ := earlier
      exact ih other before member
    · refine ⟨witness, known, ?_⟩
      intro other member
      by_cases order : witness <= other
      · exact order
      · exact False.elim (earlier ⟨other, by omega, member⟩)

-- Main design result: no preselected common trace, no cross-call sortedness
-- hypothesis. The reference run is constructed using global least-event rules.
theorem completed_run_reference (model : Model Value Aggregate domains) (horizon : Nat)
    (independent : DomainIndependent model) (count : Nat) (initial final : State Value Aggregate)
    (run : ComposedRun model horizon count initial final) (complete : Complete model horizon final) :
    ReferenceRun model horizon count initial final := by
  induction count generalizing initial final with
  | zero => cases run; exact .done _
  | succ count ih =>
    have existsReady : exists event, Ready model horizon initial event := by
      cases run with
      | step chosen _ => exact ⟨_, chosen.1⟩
    obtain ⟨witness, ready⟩ := existsReady
    obtain ⟨event, first⟩ := exists_least (Ready model horizon initial) witness ready
    obtain ⟨rest, length, tail⟩ := extract_reference model horizon independent (count + 1)
      initial final run complete event first
    have equal : rest = count := by omega
    subst rest
    exact Run.step first (ih (fire model event initial) final tail complete)

theorem reference_unique (model : Model Value Aggregate domains) (horizon : Nat)
    (a b : Nat) (initial first second : State Value Aggregate)
    (left : ReferenceRun model horizon a initial first) (right : ReferenceRun model horizon b initial second)
    (doneLeft : Complete model horizon first) (doneRight : Complete model horizon second) : first = second := by
  induction left generalizing b second with
  | done state =>
    cases right with
    | done => rfl
    | step enabled _ => exact False.elim (complete_not_ready model horizon state doneLeft _ enabled.1)
  | @step state first event _ enabled _ ih =>
    cases right with
    | done => exact False.elim (complete_not_ready model horizon state doneRight event enabled.1)
    | @step _ _ other otherCount otherEnabled otherTail =>
      have order₁ := enabled.2 other otherEnabled.1
      have order₂ := otherEnabled.2 event enabled.1
      have same : other = event := by omega
      subst other
      exact ih _ second otherTail doneLeft doneRight

theorem hierarchical_observation (model : Model Value Aggregate domains) (initial : Aggregate)
    (contributions : List (List (List Aggregate))) :
    model.algebra.merge initial
      (Clockwork.fold model.algebra (contributions.map (fun batches =>
        Clockwork.fold model.algebra (batches.map (Clockwork.fold model.algebra))))) =
    model.algebra.merge initial
      (Clockwork.fold model.algebra (contributions.map List.join).join) := by
  rw [Clockwork.three_level_reduction]

theorem compiled_completed_observations (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (p effects w body boundary tail)
    (site : Subcode (.domain p effects w body boundary tail) output)
    (model : Model Value Aggregate effects.length)
    (coverage : forall event, Within (model.handler event).access
      (accessAt effects (model.owner event).val))
    (horizon composedCount referenceCount : Nat) (initial composed sequential : State Value Aggregate)
    (scheduled : ComposedRun model horizon composedCount initial composed)
    (reference : ReferenceRun model horizon referenceCount initial sequential)
    (doneScheduled : Complete model horizon composed) (doneReference : Complete model horizon sequential) :
    composed.store = sequential.store /\ composed.aggregate = sequential.aggregate /\
      composed.pending = sequential.pending := by
  have same := reference_unique model horizon composedCount referenceCount initial composed sequential
    (completed_run_reference model horizon
      (compiled_domain_independent nodes input output accepted p effects w body boundary tail site model coverage)
      composedCount initial composed scheduled doneScheduled) reference doneScheduled doneReference
  cases same
  exact ⟨rfl, rfl, rfl⟩

-- Event/domain ownership is part of the abstract binding, not a claim about a
-- C++ queue implementation. The compiler independently proves the plan valid.
structure PlanBinding (nodes : List Nat) (plan : Plan)
    (model : Model Value Aggregate domains) where
  node : Nat -> Nat
  known : forall event, List.Mem (node event) nodes
  arity : plan.length = domains
  ownerMatches : forall event, locateOwner (node event) plan = some (model.owner event).val

-- This design theorem covers a local event dispatcher in reference order.
-- It does not silently interpret arbitrary Filter/Choice bodies as this model.
inductive SequentialDispatcher : Code -> Prop
  | execute (handlers : List Access) : SequentialDispatcher (.execute false handlers)
  | prelude (bound : Bound) {body : Code} : SequentialDispatcher body ->
      SequentialDispatcher (.seq (.drain bound) body)

def handlerDeclarations (code : Code) : List Access :=
  ((executionSites code).map Prod.snd).join

structure ProgramBinding (nodes : List Nat) (plan : Plan) (body : Code)
    (model : Model Value Aggregate domains) extends PlanBinding nodes plan model where
  dispatcher : SequentialDispatcher body
  handlerDeclared : forall event, List.Mem (model.handler event).access (handlerDeclarations body)

-- The domain admission field is interpreted here, not ignored in favor of a
-- trace-order premise. H is the active window for this completed observation.
def DomainEnabled (model : Model Value Aggregate domains) (horizon : Nat) (bound : Bound)
    (state : State Value Aggregate) (event : Nat) : Prop :=
  Ready model horizon state event /\ LocalMinimum model horizon state event /\
    exists certificate : ClockCertificate model state,
      model.time event <= evalBound horizon (certificate.safe (model.owner event)) bound

abbrev DomainRun (model : Model Value Aggregate domains) (horizon : Nat) (bound : Bound) :=
  Run (DomainEnabled model horizon bound) model

theorem effective_run_composed (model : Model Value Aggregate domains) (horizon count : Nat)
    (initial final : State Value Aggregate) (run : DomainRun model horizon .effective count initial final) :
    ComposedRun model horizon count initial final := by
  induction run with
  | done => exact .done _
  | step enabled _ ih =>
    obtain ⟨certificate, bounded⟩ := enabled.2.2
    have limit : model.time _ <= certificate.safe (model.owner _) :=
      Nat.le_trans bounded (Nat.min_le_right _ _)
    exact Run.step ⟨enabled.1, enabled.2.1, certificate, limit⟩ ih

theorem composed_run_effective (model : Model Value Aggregate domains) (horizon count : Nat)
    (initial final : State Value Aggregate) (run : ComposedRun model horizon count initial final) :
    DomainRun model horizon .effective count initial final := by
  induction run with
  | done => exact .done _
  | step enabled _ ih =>
    obtain ⟨certificate, bounded⟩ := enabled.2.2
    exact Run.step ⟨enabled.1, enabled.2.1, certificate, Nat.le_min.mpr ⟨enabled.1.2, bounded⟩⟩ ih

theorem bounded_domain {p e w body x tail code}
    (site : Subcode (.domain p e w body x tail) code) (inside : Bool)
    (bounded : Bounded inside code) : w = .effective := by
  induction site generalizing inside with
  | here => exact bounded.1
  | left _ ih | yes _ ih => exact ih inside bounded.1
  | right _ ih | no _ ih => exact ih inside bounded.2
  | loop _ ih => exact ih inside bounded
  | domain _ ih | entry _ ih => exact ih true bounded.2

-- Public design theorem: an accepted domain's own bound, resolved plan, and
-- effect summaries feed event-generating semantics and an independently chosen
-- reference execution. There is no assumed global ordering or common event log.
theorem compiled_domain_design_reference (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (p effects w body boundary tail)
    (site : Subcode (.domain p effects w body boundary tail) output)
    (model : Model Value Aggregate effects.length) (binding : ProgramBinding nodes p body model)
    (coverage : forall event, Within (model.handler event).access
      (accessAt effects (model.owner event).val))
    (horizon count : Nat) (initial final : State Value Aggregate)
    (scheduled : DomainRun model horizon w count initial final) (complete : Complete model horizon final) :
    ReferenceRun model horizon count initial final /\ Owners nodes p /\
      (forall event, locateOwner (binding.node event) p = some (model.owner event).val) := by
  have bound := bounded_domain site false (pipeline_sound nodes input output accepted).i1.1
  rw [bound] at scheduled
  exact ⟨completed_run_reference model horizon
      (compiled_domain_independent nodes input output accepted p effects w body boundary tail site model coverage)
      count initial final (effective_run_composed model horizon count initial final scheduled) complete,
    (compiled_domain_contract nodes input output accepted p effects w body boundary tail site).2.2,
    binding.ownerMatches⟩

theorem dsl_core_accepted (nodes : List Nat) (program : Program) (output : Executable)
    (accepted : compileProgram nodes program = some output) :
    compile nodes (.loop (lower false program.body)) = some output.code := by
  unfold compileProgram at accepted
  cases result : compile nodes (.loop (lower false program.body)) with
  | none => simp [result] at accepted
  | some code =>
    simp only [result, Option.map_some] at accepted
    have same := Option.some.inj accepted
    subst output
    rfl

theorem dsl_domain_design_reference (nodes : List Nat) (program : Program) (output : Executable)
    (accepted : compileProgram nodes program = some output) (p effects w body boundary tail)
    (site : Subcode (.domain p effects w body boundary tail) output.code)
    (model : Model Value Aggregate effects.length) (binding : ProgramBinding nodes p body model)
    (coverage : forall event, Within (model.handler event).access
      (accessAt effects (model.owner event).val))
    (count : Nat) (initial final : State Value Aggregate)
    (scheduled : DomainRun model program.horizon w count initial final)
    (complete : Complete model program.horizon final) :
    ReferenceRun model program.horizon count initial final /\ output.horizon = program.horizon := by
  exact ⟨(compiled_domain_design_reference nodes (.loop (lower false program.body)) output.code
    (dsl_core_accepted nodes program output accepted) p effects w body boundary tail site
    model binding coverage program.horizon count initial final scheduled complete).1,
    (dsl_pipeline_sound nodes program output accepted).1⟩

#print axioms fire_pending_balance
#print axioms composed_event_accounting
#print axioms fire_commutes
#print axioms mixed_diamond
#print axioms completed_run_reference
#print axioms compiled_completed_observations
#print axioms compiled_domain_design_reference
#print axioms dsl_domain_design_reference

end Clockwork.Core.DES
