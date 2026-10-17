import Bridge
import DSL

namespace Clockwork.Core

-- Finite execution semantics for resolved recursive IR. Domain visits and
-- external callables are explicit; this is not a C++ concurrency semantics.
structure Context where
  owner : Nat
  window : Nat
  safe : Nat
  domains : List Nat

inductive Signal where
  | route (owner : Nat)
  | announce (owner time : Nat)
  | barrier
  | globalReduce (region : Nat)
  deriving DecidableEq, Repr

structure Machine (Value : Type) where
  store : Store Value
  queues : Nat -> List Clockwork.Event
  admitted : Nat -> List Clockwork.Event
  batchValues : Nat -> Nat -> List Value
  partials : Nat -> Nat -> List Value
  totals : Nat -> Value
  plan : Plan
  outgoing : List Pending
  delivered : List (Prod Nat Pending)
  frontiers : Nat -> Nat
  signals : List Signal
  steps : Nat

def update (values : Nat -> Item) (key : Nat) (value : Item) : Nat -> Item :=
  fun other => if other = key then value else values other

@[simp] theorem update_here (values : Nat -> Item) (key : Nat) (value : Item) :
    update values key value key = value := by simp [update]

def admitQueue (ctx : Context) (bound : Bound) (state : Machine Value) : Machine Value :=
  let result := Clockwork.drain (evalBound ctx.window ctx.safe bound) (state.queues ctx.owner)
  { state with queues := update state.queues ctx.owner result.2,
               admitted := update state.admitted ctx.owner (state.admitted ctx.owner ++ result.1) }

def batchFold (algebra : Clockwork.Reduction Value) (ctx : Context) (region : Nat)
    (state : Machine Value) : Machine Value :=
  let value := Clockwork.fold algebra (state.batchValues ctx.owner region)
  { state with
    batchValues := update state.batchValues ctx.owner (update (state.batchValues ctx.owner) region []),
    partials := update state.partials ctx.owner
      (update (state.partials ctx.owner) region (state.partials ctx.owner region ++ [value])) }

def partitionFold (algebra : Clockwork.Reduction Value) (ctx : Context) (region : Nat)
    (state : Machine Value) : Machine Value :=
  { state with
    partials := update state.partials ctx.owner
      (update (state.partials ctx.owner) region [Clockwork.fold algebra (state.partials ctx.owner region)]) }

def globalFold (algebra : Clockwork.Reduction Value) (ctx : Context) (region : Nat)
    (state : Machine Value) : Machine Value :=
  let contributions := ctx.domains.map (fun owner => state.partials owner region)
  { state with
    totals := update state.totals region (Clockwork.fold algebra contributions.join),
    partials := fun owner => if ctx.domains.contains owner then update (state.partials owner) region []
                            else state.partials owner,
    signals := state.signals ++ [.globalReduce region] }

def routeOutputs (ctx : Context) (state : Machine Value) : Machine Value :=
  { state with
    outgoing := [],
    delivered := state.delivered ++
      route (fun node => (locateOwner node state.plan).getD 0) state.outgoing,
    signals := state.signals ++ [.route ctx.owner] }

def announce (ctx : Context) (bound : Bound) (state : Machine Value) : Machine Value :=
  let time := evalBound ctx.window ctx.safe bound
  { state with frontiers := update state.frontiers ctx.owner time,
               signals := state.signals ++ [.announce ctx.owner time] }

def executeBoundary (ctx : Context) : Boundary -> Machine Value -> Machine Value
  | .announceRoute bound, state => routeOutputs ctx (announce ctx bound state)
  | .routeAnnounce bound, state => announce ctx bound (routeOutputs ctx state)

def executeTail (algebra : Clockwork.Reduction Value) (ctx : Context) :
    List TailOp -> Machine Value -> Machine Value
  | [], state => state
  | .barrier :: rest, state =>
      executeTail algebra ctx rest { state with signals := state.signals ++ [.barrier] }
  | .globalReduce region :: rest, state => executeTail algebra ctx rest (globalFold algebra ctx region state)

-- These are binding/runtime inputs, not facts manufactured by compilation.
-- Realization preserves each declared occurrence. A repeated handler invocation
-- must have its own declaration (or a separately modeled serial lane).
structure Runtime (Value : Type) where
  algebra : Clockwork.Reduction Value
  actions : Bool -> List Access -> Context -> Machine Value -> List (Action Value)
  realizes : forall parallel group ctx state,
    Permutation group ((actions parallel group ctx state).map (fun a => a.handler.access))
  serialRealizes : forall group ctx state,
    (actions false group ctx state).map (fun a => a.handler.access) = group
  transform : Transform -> Context -> Machine Value -> Machine Value
  commit : Context -> Machine Value -> Machine Value
  commitStore : forall ctx state, (commit ctx state).store = state.store
  reassign : Plan -> Context -> Machine Value -> Machine Value
  guard : Nat -> Context -> Machine Value -> Bool
  continueLoop : Context -> Machine Value -> Bool
  bounds : Plan -> Context -> Nat -> Machine Value -> Prod Nat Nat

inductive ExecutionMode where
  | scheduled
  | serialGroups

-- Both modes record the *requested* calls. serialGroups executes a sorted copy
-- of each parallel call; retaining the request makes control-flow comparison
-- and the executed scheduled-mode trace unambiguous.
structure Call (Value : Type) where
  parallel : Bool
  actions : List (Action Value)

structure ExecutionState (Value : Type) where
  machine : Machine Value
  calls : List (Call Value)

def changeMachine (f : Machine Value -> Machine Value) (state : ExecutionState Value) :
    ExecutionState Value := { state with machine := f state.machine }

def executeCall (runtime : Runtime Value) (mode : ExecutionMode) (parallel : Bool)
    (group : List Access) (ctx : Context) (state : ExecutionState Value) : ExecutionState Value :=
  let actions := runtime.actions parallel group ctx state.machine
  let ordered := match mode, parallel with
    | .serialGroups, true => referenceOrder actions
    | _, _ => actions
  let next := { state.machine with store := runActions ordered state.machine.store }
  { machine := runtime.commit ctx next,
    calls := state.calls ++ [{parallel := parallel, actions := actions}] }

def visitDomains (runtime : Runtime Value) (plan : Plan) (parent : Context)
    (bound : Bound) (boundary : Boundary)
    (body : Context -> ExecutionState Value -> Option (ExecutionState Value)) :
    List Nat -> ExecutionState Value -> Option (ExecutionState Value)
  | [], state => some state
  | owner :: rest, state => do
      let times := runtime.bounds plan parent owner state.machine
      let ctx : Context := ⟨owner, times.1, times.2, List.range plan.length⟩
      let next <- body ctx (changeMachine (admitQueue ctx bound) state)
      visitDomains runtime plan parent bound boundary body rest
        (changeMachine (executeBoundary ctx boundary) next)

-- Fuel bounds derivation height, including loop unfolding and nested calls.
-- none means fuel exhaustion or invalid IR, not model nontermination proved.
def evaluate (runtime : Runtime Value) (mode : ExecutionMode) :
    Nat -> Code -> Context -> ExecutionState Value -> Option (ExecutionState Value)
  | 0, _, _, _ => none
  | fuel + 1, code, ctx, state =>
    match code with
    | .stop => some state
    | .invalid => none
    | .drain bound => some (changeMachine (admitQueue ctx bound) state)
    | .execute parallel group => some (executeCall runtime mode parallel group ctx state)
    | .transform fn => some (changeMachine (runtime.transform fn ctx) state)
    | .reduceBatch region => some (changeMachine (batchFold runtime.algebra ctx region) state)
    | .reducePair region => some (changeMachine
        (fun s => partitionFold runtime.algebra ctx region (batchFold runtime.algebra ctx region s)) state)
    | .seq first second => do
        let next <- evaluate runtime mode fuel first ctx state
        evaluate runtime mode fuel second ctx next
    | .loop body => if runtime.continueLoop ctx state.machine then do
        let next <- evaluate runtime mode fuel body ctx state
        evaluate runtime mode fuel (.loop body) ctx next
      else some state
    | .branch guard yes no =>
        evaluate runtime mode fuel (if runtime.guard guard ctx state.machine then yes else no) ctx state
    | .domain plan _ bound body boundary tail => do
        let start := changeMachine (fun s => {s with plan := plan}) state
        let next <- visitDomains runtime plan ctx bound boundary
          (evaluate runtime mode fuel body) (List.range plan.length) start
        pure (changeMachine (executeTail runtime.algebra {ctx with domains := List.range plan.length} tail) next)
    | .entry fn plan effects bound body boundary tail =>
        evaluate runtime mode fuel (.domain plan effects bound body boundary tail) ctx
          (changeMachine (runtime.transform fn ctx) state)
    | .reassign plan => some (changeMachine
        (fun s => {runtime.reassign plan ctx s with plan := plan}) state)

theorem executeCall_reference (runtime : Runtime Value) (parallel : Bool) (group : List Access)
    (safe : parallel = true -> GroupSafe group) (ctx : Context) (state : ExecutionState Value) :
    executeCall runtime .scheduled parallel group ctx state =
      executeCall runtime .serialGroups parallel group ctx state := by
  cases parallel
  · rfl
  · have independent := groupSafe_permutation (runtime.realizes true group ctx state.machine) (safe rfl)
    have same := reference_equivalence _ (groupSafe_conflictOrdered _ independent) state.machine.store
    simp only [executeCall]
    rw [same]

-- This theorem covers recursive control flow, domain visits, queues, pending
-- outputs, reductions, and boundary effects of the specified interpreter.
-- It serializes each checked parallel call, retaining the program's order of
-- different calls. Global timestamp sorting needs the additional order contract
-- in compiled_handler_trace_reference below.
theorem evaluate_reference (runtime : Runtime Value) (fuel : Nat) (code : Code)
    (safe : RaceFree code) (ctx : Context) (state : ExecutionState Value) :
    evaluate runtime .scheduled fuel code ctx state =
      evaluate runtime .serialGroups fuel code ctx state := by
  induction fuel generalizing code ctx state with
  | zero => rfl
  | succ fuel ih =>
    cases code with
    | execute parallel group => exact congrArg some (executeCall_reference runtime parallel group safe ctx state)
    | seq first second =>
      simp only [evaluate]
      rw [ih first safe.1 ctx state]
      cases evaluate runtime .serialGroups fuel first ctx state with
      | none => rfl
      | some next => exact ih second safe.2 ctx next
    | loop body =>
      simp only [evaluate]
      split
      · rw [ih body safe ctx state]
        cases evaluate runtime .serialGroups fuel body ctx state with
        | none => rfl
        | some next => exact ih (.loop body) safe ctx next
      · rfl
    | branch guard yes no =>
      simp only [evaluate]
      split
      · exact ih yes safe.1 ctx state
      · exact ih no safe.2 ctx state
    | domain plan effects bound body boundary tail =>
      have same : evaluate runtime .scheduled fuel body = evaluate runtime .serialGroups fuel body := by
        funext inner next
        exact ih body safe.2 inner next
      simp only [evaluate]
      rw [same]
    | entry fn plan effects bound body boundary tail =>
      exact ih (.domain plan effects bound body boundary tail) safe ctx
        (changeMachine (runtime.transform fn ctx) state)
    | _ => rfl

theorem compiled_execution_reference (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (runtime : Runtime Value)
    (fuel : Nat) (ctx : Context) (state : ExecutionState Value) :
    evaluate runtime .scheduled fuel output ctx state =
      evaluate runtime .serialGroups fuel output ctx state :=
  evaluate_reference runtime fuel output (pipeline_sound nodes input output accepted).i4 ctx state

theorem dsl_execution_reference (nodes : List Nat) (program : Program) (output : Executable)
    (accepted : compileProgram nodes program = some output) (runtime : Runtime Value)
    (fuel : Nat) (ctx : Context) (state : ExecutionState Value) :
    evaluate runtime .scheduled fuel output.code ctx state =
      evaluate runtime .serialGroups fuel output.code ctx state :=
  evaluate_reference runtime fuel output.code (dsl_pipeline_sound nodes program output accepted).2.i4 ctx state

#print axioms compiled_execution_reference
#print axioms dsl_execution_reference

end Clockwork.Core
