import Execution

namespace Clockwork.Core

def CallSafe (call : Call Value) : Prop :=
  call.parallel = true -> GroupSafe (call.actions.map (fun a => a.handler.access))

def CallsSafe (calls : List (Call Value)) : Prop :=
  forall call, List.Mem call calls -> CallSafe call

theorem callsSafe_append (before after : List (Call Value))
    (first : CallsSafe before) (second : CallsSafe after) : CallsSafe (before ++ after) := by
  intro call member
  cases member_append call before after member with
  | inl member => exact first call member
  | inr member => exact second call member

theorem executeCall_safe (runtime : Runtime Value) (parallel : Bool) (group : List Access)
    (safe : parallel = true -> GroupSafe group) (ctx : Context) (state : ExecutionState Value)
    (prior : CallsSafe state.calls) :
    CallsSafe (executeCall runtime .scheduled parallel group ctx state).calls := by
  apply callsSafe_append _ _ prior
  intro call member isParallel
  cases member with
  | head => exact groupSafe_permutation (runtime.realizes parallel group ctx state.machine) (safe isParallel)
  | tail _ absent => cases absent

theorem visitDomains_safe (runtime : Runtime Value) (plan : Plan) (parent : Context)
    (bound : Bound) (boundary : Boundary)
    (body : Context -> ExecutionState Value -> Option (ExecutionState Value))
    (bodySafe : forall ctx state result, CallsSafe state.calls -> body ctx state = some result ->
      CallsSafe result.calls)
    (owners : List Nat) (state result : ExecutionState Value) (prior : CallsSafe state.calls)
    (run : visitDomains runtime plan parent bound boundary body owners state = some result) :
    CallsSafe result.calls := by
  induction owners generalizing state result with
  | nil => cases Option.some.inj run; exact prior
  | cons owner rest ih =>
    let times := runtime.bounds plan parent owner state.machine
    let ctx : Context := ⟨owner, times.1, times.2, List.range plan.length⟩
    change (body ctx (changeMachine (admitQueue ctx bound) state) >>= fun next =>
      visitDomains runtime plan parent bound boundary body rest
        (changeMachine (executeBoundary ctx boundary) next)) = some result at run
    cases h : body ctx (changeMachine (admitQueue ctx bound) state) with
    | none => simp [h] at run
    | some next =>
      have nextSafe := bodySafe ctx (changeMachine (admitQueue ctx bound) state) next prior h
      exact ih (changeMachine (executeBoundary ctx boundary) next) result nextSafe
        (by simpa [h] using run)

theorem evaluate_calls_safe (runtime : Runtime Value) (fuel : Nat) (code : Code)
    (safe : RaceFree code) (ctx : Context) (state result : ExecutionState Value)
    (prior : CallsSafe state.calls)
    (run : evaluate runtime .scheduled fuel code ctx state = some result) :
    CallsSafe result.calls := by
  induction fuel generalizing code ctx state result with
  | zero => cases run
  | succ fuel ih =>
    cases code with
    | invalid => cases run
    | execute parallel group =>
      cases Option.some.inj run
      exact executeCall_safe runtime parallel group safe ctx state prior
    | seq first second =>
      change (evaluate runtime .scheduled fuel first ctx state >>= fun next =>
        evaluate runtime .scheduled fuel second ctx next) = some result at run
      cases h : evaluate runtime .scheduled fuel first ctx state with
      | none => simp [h] at run
      | some next =>
        exact ih second safe.2 ctx next result (ih first safe.1 ctx state next prior h)
          (by simpa [h] using run)
    | loop body =>
      simp only [evaluate] at run
      split at run
      · cases h : evaluate runtime .scheduled fuel body ctx state with
        | none => simp [h] at run
        | some next =>
          exact ih (.loop body) safe ctx next result (ih body safe ctx state next prior h)
            (by simpa [h] using run)
      · cases Option.some.inj run; exact prior
    | branch guard yes no =>
      simp only [evaluate] at run
      split at run
      · exact ih yes safe.1 ctx state result prior run
      · exact ih no safe.2 ctx state result prior run
    | domain plan effects bound body boundary tail =>
      simp only [evaluate] at run
      let start := changeMachine (fun s => {s with plan := plan}) state
      cases h : visitDomains runtime plan ctx bound boundary
          (evaluate runtime .scheduled fuel body) (List.range plan.length) start with
      | none => simp [start, h] at run
      | some next =>
        have nextSafe := visitDomains_safe runtime plan ctx bound boundary
          (evaluate runtime .scheduled fuel body)
          (fun inner before after known executed => ih body safe.2 inner before after known executed)
          (List.range plan.length) start next prior h
        have same : changeMachine
            (executeTail runtime.algebra {ctx with domains := List.range plan.length} tail) next = result := by
          simpa [start, h] using run
        rw [<- same]
        exact nextSafe
    | entry fn plan effects bound body boundary tail =>
      exact ih (.domain plan effects bound body boundary tail) safe ctx
        (changeMachine (runtime.transform fn ctx) state) result prior run
    | _ => cases Option.some.inj run; exact prior

def handlerTrace (calls : List (Call Value)) : List (Action Value) :=
  (calls.map (fun call => call.actions)).join

-- Runtime contract for calls that were not checked as parallel groups.
def SerialCallsSorted (calls : List (Call Value)) : Prop :=
  forall call, List.Mem call calls -> call.parallel = false -> PrioritySorted call.actions

-- A sufficient cross-call order contract: calls occupy ordered reference bands.
-- This is deliberately stated independently of ConflictOrdered. It is not an
-- output of the compiler and is stronger than merely preserving conflicts.
def CallsChronological : List (Call Value) -> Prop
  | [] => True
  | call :: rest =>
      (forall earlier, List.Mem earlier call.actions ->
        forall later, List.Mem later (handlerTrace rest) -> earlier.priority <= later.priority) /\
      CallsChronological rest

theorem prioritySorted_conflictOrdered (actions : List (Action Value))
    (sorted : PrioritySorted actions) : ConflictOrdered actions := by
  induction actions with
  | nil => trivial
  | cons action rest ih =>
    exact ⟨(fun later member inverse => False.elim (by have := sorted.1 later member; omega)), ih sorted.2⟩

theorem conflictOrdered_append (before after : List (Action Value))
    (first : ConflictOrdered before) (second : ConflictOrdered after)
    (bands : forall earlier, List.Mem earlier before ->
      forall later, List.Mem later after -> earlier.priority <= later.priority) :
    ConflictOrdered (before ++ after) := by
  induction before with
  | nil => exact second
  | cons action rest ih =>
    constructor
    · intro later member inverse
      cases member_append later rest after member with
      | inl member => exact first.1 later member inverse
      | inr member => have := bands action (.head rest) later member; omega
    · exact ih first.2 (fun earlier member => bands earlier (.tail action member))

theorem calls_conflictOrdered (calls : List (Call Value))
    (safe : CallsSafe calls) (serial : SerialCallsSorted calls)
    (bands : CallsChronological calls) : ConflictOrdered (handlerTrace calls) := by
  induction calls with
  | nil => trivial
  | cons call rest ih =>
    have first : ConflictOrdered call.actions := by
      cases h : call.parallel with
      | false => exact prioritySorted_conflictOrdered _ (serial call (.head rest) h)
      | true => exact groupSafe_conflictOrdered _ (safe call (.head rest) h)
    exact conflictOrdered_append call.actions (handlerTrace rest) first
      (ih (fun c hc => safe c (.tail call hc)) (fun c hc => serial c (.tail call hc)) bands.2) bands.1

-- Compiler -> actual finite semantic execution -> checked calls -> conflict
-- order -> the existing timestamp/tie reference equivalence theorem.
-- This concerns the handler subtrace, not erasure of transform/reduction effects.
theorem compiled_handler_trace_reference (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (runtime : Runtime Value)
    (fuel : Nat) (ctx : Context) (initial : Machine Value) (result : ExecutionState Value)
    (run : evaluate runtime .scheduled fuel output ctx ⟨initial, []⟩ = some result)
    (serial : SerialCallsSorted result.calls) (bands : CallsChronological result.calls)
    (state : Store Value) :
    runActions (handlerTrace result.calls) state =
      runActions (referenceOrder (handlerTrace result.calls)) state := by
  have safe := evaluate_calls_safe runtime fuel output
    (pipeline_sound nodes input output accepted).i4 ctx ⟨initial, []⟩ result
    (by intro call member; cases member) run
  exact reference_equivalence _ (calls_conflictOrdered result.calls safe serial bands) state

#print axioms evaluate_calls_safe
#print axioms compiled_handler_trace_reference

end Clockwork.Core
