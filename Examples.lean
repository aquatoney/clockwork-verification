import ExecutionObligations

namespace Clockwork.Core.Examples

def addition : Clockwork.Reduction Nat where
  zero := 0
  merge := Nat.add
  leftIdentity := Nat.zero_add
  rightIdentity := Nat.add_zero
  associative := Nat.add_assoc
  commutative := Nat.add_comm

-- Actual store effects, with proofs of the declared frame/locality contracts.
def writer (access : Access) : Handler Nat where
  access := access
  step state key := if access.writes.contains key then access.handler + 1 else state key
  frame := by
    intro state key outside
    by_cases inside : access.writes.contains key = true
    · exact False.elim (outside (List.mem_of_elem_eq_true inside))
    · simp [inside]
  locality := by
    intro before after _ key written
    have inside : access.writes.contains key = true := List.elem_eq_true_of_mem written
    simp [inside]

def actionFor (ctx : Context) (access : Access) : Action Nat :=
  ⟨ctx.owner * 10 + access.handler, writer access⟩

def requested (parallel : Bool) (group : List Access) : List Access :=
  if parallel then match group with
    | a :: b :: rest => b :: a :: rest
    | other => other
  else group

theorem action_accesses (ctx : Context) (group : List Access) :
    ((group.map (actionFor ctx)).map (fun a => a.handler.access)) = group := by
  induction group with
  | nil => rfl
  | cons access rest ih => simp only [List.map_cons, actionFor, writer, ih]

theorem requested_permutation (parallel : Bool) (group : List Access) :
    Permutation group (requested parallel group) := by
  cases parallel
  · exact .refl _
  · cases group with
    | nil => exact .refl _
    | cons a rest =>
      cases rest with
      | nil => exact .refl _
      | cons b rest => exact .swap a b rest

def runtime : Runtime Nat where
  algebra := addition
  actions parallel group ctx _ := (requested parallel group).map (actionFor ctx)
  realizes := by
    intro parallel group ctx _
    rw [action_accesses]
    exact requested_permutation parallel group
  serialRealizes := by intro group ctx _; exact action_accesses ctx group
  transform fn _ state := {state with
    store := update state.store fn.name (state.store fn.name + 1), steps := state.steps + 1}
  commit ctx state := {state with
    admitted := update state.admitted ctx.owner [],
    batchValues := update state.batchValues ctx.owner
      (update (state.batchValues ctx.owner) 7 [ctx.owner + 1]), steps := state.steps + 1}
  commitStore := by intros; rfl
  reassign _ _ state := state
  guard key _ state := state.store key == 0
  continueLoop _ state := state.steps < 2
  bounds _ parent _ _ := (parent.window, parent.safe)

def root : Context := ⟨0, 10, 7, [0]⟩
def early₀ : Clockwork.Event := ⟨5, 0⟩
def early₁ : Clockwork.Event := ⟨6, 1⟩
def future : Clockwork.Event := ⟨15, 2⟩

def initial : Machine Nat where
  store := fun _ => 0
  queues := fun _ => [early₀, early₁, future]
  admitted := fun _ => []
  batchValues := fun _ _ => []
  partials := fun _ _ => []
  totals := fun _ => 0
  plan := []
  outgoing := [⟨1, early₀⟩]
  delivered := []
  frontiers := fun _ => 0
  signals := []
  steps := 0

def input : Code :=
  .domain samplePlan [lane0, lane1] (.literal 99)
    (.seq (.drain (.literal 99)) (.seq (.execute true [lane0, lane1]) (.reduceBatch 7)))
    (.announceRoute (.literal 99)) []

def output : Code := normalize input
theorem accepted : compile [0, 1] input = some output := by decide

def result : ExecutionState Nat :=
  (evaluate runtime .scheduled 10 output root ⟨initial, []⟩).getD ⟨initial, []⟩

-- Nonempty execution, not just equal failure/fuel exhaustion in two modes.
theorem executed : evaluate runtime .scheduled 10 output root ⟨initial, []⟩ = some result := by rfl
example : result.calls.length = 2 := by decide
example : result.machine.store 0 = 1 /\ result.machine.store 1 = 2 := by decide
example : result.machine.queues 0 = [future] := by decide
example : result.machine.totals 7 = 3 := by decide
example : result.machine.signals =
    [.route 0, .announce 0 7, .route 1, .announce 1 7, .barrier, .globalReduce 7] := by decide
example : result.machine.delivered.map Prod.snd = [⟨1, early₀⟩] := by decide

example : evaluate runtime .serialGroups 10 output root ⟨initial, []⟩ = some result := by
  rw [<- compiled_execution_reference [0, 1] input output accepted runtime 10 root ⟨initial, []⟩]
  exact executed

-- The chosen schedule actually inverts the two independent handlers.
example : (runtime.actions true [lane0, lane1] root initial).map (fun a => a.priority) = [1, 0] := by decide
example : ((referenceOrder (runtime.actions true [lane0, lane1] root initial)).map
    (fun a => a.priority)) = [0, 1] := by decide
example (state : Store Nat) :
    runActions (runtime.actions true [lane0, lane1] root initial) state =
      runActions (referenceOrder (runtime.actions true [lane0, lane1] root initial)) state := by
  apply compiled_parallel_reference [0, 1] input output accepted [lane0, lane1]
    (by exact .head [])
  exact runtime.realizes true [lane0, lane1] root initial

theorem serial_calls_sorted : SerialCallsSorted result.calls := by
  intro call member impossible
  cases member with
  | head => cases impossible
  | tail _ member =>
    cases member with
    | head => cases impossible
    | tail _ absent => cases absent

theorem calls_chronological : CallsChronological result.calls := by
  constructor
  · intro earlier first later second
    cases first with
    | head =>
      cases second with
      | head => decide
      | tail _ second =>
        cases second with
        | head => decide
        | tail _ absent => cases absent
    | tail _ first =>
      cases first with
      | head =>
        cases second with
        | head => decide
        | tail _ second =>
          cases second with
          | head => decide
          | tail _ absent => cases absent
      | tail _ absent => cases absent
  · constructor
    · intro earlier _ later absent; cases absent
    · trivial

example (state : Store Nat) : runActions (handlerTrace result.calls) state =
    runActions (referenceOrder (handlerTrace result.calls)) state :=
  compiled_handler_trace_reference [0, 1] input output accepted runtime 10 root initial result
    executed serial_calls_sorted calls_chronological state

def dslOutput : Executable := ⟨10, normalize (.loop (lower false partitionBatch.body))⟩
theorem dsl_accepted : compileProgram [0, 1] partitionBatch = some dslOutput := by decide
example : (evaluate runtime .scheduled 10 dslOutput.code root ⟨initial, []⟩).isSome = true := by decide
example : evaluate runtime .scheduled 10 dslOutput.code root ⟨initial, []⟩ =
    evaluate runtime .serialGroups 10 dslOutput.code root ⟨initial, []⟩ :=
  dsl_execution_reference [0, 1] partitionBatch dslOutput dsl_accepted runtime 10 root ⟨initial, []⟩

-- Exercise finite loop unfolding and a state-dependent branch.
def controlFlow : Code := .seq (.branch 0 .stop (.execute false [lane0]))
  (.loop (.transform ⟨99, true⟩))
example : ((evaluate runtime .scheduled 6 controlFlow root ⟨initial, []⟩).getD
    ⟨initial, []⟩).machine.store 99 = 2 := by decide
example : evaluate runtime .scheduled 1 controlFlow root ⟨initial, []⟩ = none := by rfl

-- Unsafe parallel occurrences and overlapping ownership are still rejected.
example : compile [0, 1] (.execute true [lane0, lane0]) = none := by decide
example : compile [0, 1] (.domain [[0], [0, 1]] [] .effective .stop
    (.routeAnnounce .effective) []) = none := by decide

-- A singleton declaration cannot be inflated to two conflicting occurrences.
example : Not (Permutation [lane0] [lane0, lane0]) := by
  intro inflated
  have count := permutation_count lane0 inflated
  simp [lane0] at count

-- Compiler checks do not establish cross-call reference order.
def conflicting : Access := ⟨0, [], [0]⟩
def setValue (value : Nat) : Handler Nat where
  access := conflicting
  step state key := if key = 0 then value else state key
  frame := by
    intro state key outside
    by_cases zero : key = 0
    · subst key; exact False.elim (outside (.head []))
    · simp [zero]
  locality := by
    intro before after _ key written
    cases written with
    | head => rfl
    | tail _ absent => cases absent

def late : Action Nat := ⟨2, setValue 1⟩
def earlier : Action Nat := ⟨1, setValue 2⟩
example : compile [] (.seq (.execute true [conflicting]) (.execute true [conflicting])) =
    some (.seq (.execute true [conflicting]) (.execute true [conflicting])) := by decide
example : runActions [late, earlier] (fun _ => 0) 0 = 2 := by decide
example : runActions (referenceOrder [late, earlier]) (fun _ => 0) 0 = 1 := by decide

end Clockwork.Core.Examples
