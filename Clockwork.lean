import Lean

namespace Clockwork

-- Queue semantics for one conservative domain after MinBound resolution.
structure Event where
  time : Nat
  identity : Nat
  deriving DecidableEq

def effective (window safe : Nat) : Nat := min window safe

def drain (bound : Nat) : List Event -> Prod (List Event) (List Event)
  | [] => ([], [])
  | e :: rest =>
    let (admitted, pending) := drain bound rest
    if e.time <= bound then (e :: admitted, pending)
    else (admitted, e :: pending)

def allThrough (bound : Nat) : List Event -> Prop
  | [] => True
  | e :: rest => e.time <= bound /\ allThrough bound rest

def occurrences (target : Event) : List Event -> Nat
  | [] => 0
  | e :: rest => (if e = target then 1 else 0) + occurrences target rest

theorem drain_admission (bound : Nat) (events : List Event) :
    allThrough bound (drain bound events).1 := by
  induction events with
  | nil => trivial
  | cons e rest ih =>
    by_cases h : e.time <= bound
    case pos => simpa [drain, h, allThrough] using And.intro h ih
    case neg => simpa [drain, h] using ih

theorem drain_safe (window safe : Nat) (events : List Event) :
    allThrough safe (drain (effective window safe) events).1 := by
  have weaken : forall es : List Event,
      allThrough (effective window safe) es -> allThrough safe es := by
    intro es
    induction es with
    | nil => simp [allThrough]
    | cons e rest ih =>
      intro h
      exact And.intro (Nat.le_trans h.1 (Nat.min_le_right window safe)) (ih h.2)
  exact weaken _ (drain_admission _ events)

theorem drain_conservation (bound : Nat) (events : List Event) (target : Event) :
    occurrences target (drain bound events).1 +
      occurrences target (drain bound events).2 = occurrences target events := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    by_cases h : e.time <= bound
    case pos =>
      simp only [drain, h, if_true, occurrences]
      omega
    case neg =>
      simp only [drain, h, if_false, occurrences]
      omega

theorem admitted_available (window safe : Nat) (events : List Event)
    (available : Event -> Prop)
    (certificate : forall e, e.time <= safe -> available e) :
    forall e, List.Mem e (drain (effective window safe) events).1 -> available e := by
  have through := drain_safe window safe events
  generalize drain (effective window safe) events = result at *
  intro e member
  have bounded : forall es : List Event, allThrough safe es ->
      List.Mem e es -> e.time <= safe := by
    intro es
    induction es with
    | nil => intro _ mem; cases mem
    | cons head rest ih =>
      intro h mem
      cases mem with
      | head => exact h.1
      | tail _ mem => exact ih h.2 mem
  exact certificate e (bounded result.1 through member)

-- Local sync rewrite, with its effective value already in lexical scope.
inductive Bound where
  | literal (time : Nat)
  | effective
  deriving DecidableEq

inductive Op where
  | drain (bound : Bound)
  | execute (handler : Nat)
  | route
  | announce (bound : Bound)
  | batchReduce
  | partitionReduce
  | barrier
  | globalReduce
  deriving DecidableEq

def retarget : Bound -> Bound
  | .literal _ => .effective
  | .effective => .effective

@[simp] theorem retarget_effective (b : Bound) : retarget b = .effective := by
  cases b <;> rfl

def tighten : List Op -> List Op := List.map fun op =>
  match op with
  | .drain b => .drain (retarget b)
  | other => other

def normalizeSync : List Op -> List Op
  | .announce b :: .route :: rest =>
      .route :: .announce (retarget b) :: normalizeSync rest
  | .announce b :: rest => .announce (retarget b) :: normalizeSync rest
  | op :: rest => op :: normalizeSync rest
  | [] => []

def drainBounds : List Op -> List Bound
  | [] => []
  | .drain b :: rest => b :: drainBounds rest
  | _ :: rest => drainBounds rest

theorem tighten_establishes (ops : List Op) :
    drainBounds (tighten ops) = (drainBounds ops).map (fun _ => Bound.effective) := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      simp only [tighten, retarget_effective] at ih
      cases op <;> simp [tighten, drainBounds, ih]

theorem sync_preserves_drain_bounds (ops : List Op) :
    drainBounds (normalizeSync ops) = drainBounds ops := by
  match ops with
  | [] => rfl
  | .announce b :: .route :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
  | .announce b :: [] => rfl
  | .announce b :: (.drain d :: rest) =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds (.drain d :: rest)
  | .announce b :: (.execute h :: rest) =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds (.execute h :: rest)
  | .announce b :: (.announce c :: rest) =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds (.announce c :: rest)
  | .announce b :: (.batchReduce :: rest) =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds (.batchReduce :: rest)
  | .announce b :: (.partitionReduce :: rest) =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds (.partitionReduce :: rest)
  | .announce b :: (.barrier :: rest) =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds (.barrier :: rest)
  | .announce b :: (.globalReduce :: rest) =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds (.globalReduce :: rest)
  | .drain b :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
  | .execute h :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
  | .route :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
  | .batchReduce :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
  | .partitionReduce :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
  | .barrier :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
  | .globalReduce :: rest =>
      simpa [normalizeSync, drainBounds] using sync_preserves_drain_bounds rest
termination_by ops.length

theorem sync_boundary (literalTime : Nat) (rest : List Op) :
    normalizeSync (.announce (.literal literalTime) :: .route :: rest) =
      .route :: .announce .effective :: normalizeSync rest := by
  rfl

theorem sync_preserves_tightening (ops : List Op) :
    drainBounds (normalizeSync (tighten ops)) =
      (drainBounds ops).map (fun _ => Bound.effective) := by
  rw [sync_preserves_drain_bounds, tighten_establishes]

-- The reduction proof applies to any declared associative merge algebra.
structure Reduction (Value : Type) where
  zero : Value
  merge : Value -> Value -> Value
  leftIdentity : forall x, merge zero x = x
  rightIdentity : forall x, merge x zero = x
  associative : forall x y z, merge (merge x y) z = merge x (merge y z)
  commutative : forall x y, merge x y = merge y x

def fold (algebra : Reduction Value) : List Value -> Value
  | [] => algebra.zero
  | v :: rest => algebra.merge v (fold algebra rest)

theorem fold_append (algebra : Reduction Value) (xs ys : List Value) :
    fold algebra (xs ++ ys) = algebra.merge (fold algebra xs) (fold algebra ys) := by
  induction xs with
  | nil => simp [fold, algebra.leftIdentity]
  | cons x xs ih => simp [fold, ih, algebra.associative]

theorem fold_groups (algebra : Reduction Value) (groups : List (List Value)) :
    fold algebra (groups.map (fold algebra)) = fold algebra groups.join := by
  induction groups with
  | nil => rfl
  | cons group groups ih => simp [fold, fold_append, ih]

theorem three_level_reduction (algebra : Reduction Value)
    (domains : List (List (List Value))) :
    fold algebra (domains.map (fun batches => fold algebra (batches.map (fold algebra)))) =
      fold algebra (domains.map List.join).join := by
  induction domains with
  | nil => rfl
  | cons batches domains ih =>
      simp only [List.map_cons, List.join_cons, fold]
      rw [fold_groups, ih, fold_append]

-- Adjacent independent executions generate the reference reordering argument.
def run (step : Handler -> State -> State) : List Handler -> State -> State
  | [], state => state
  | h :: rest, state => run step rest (step h state)

def Independent (step : Handler -> State -> State) (a b : Handler) : Prop :=
  forall state, step b (step a state) = step a (step b state)

theorem independent_swap (step : Handler -> State -> State) (a b : Handler)
    (h : Independent step a b) (rest : List Handler) (state : State) :
    run step (a :: b :: rest) state = run step (b :: a :: rest) state := by
  simp only [run]
  rw [h state]

theorem reduction_steps_independent (algebra : Reduction Value) (a b : Value) :
    Independent (fun value acc => algebra.merge acc value) a b := by
  intro state
  change algebra.merge (algebra.merge state a) b = algebra.merge (algebra.merge state b) a
  rw [algebra.associative state a b, algebra.associative state b a,
      algebra.commutative a b]

theorem run_append (step : Handler -> State -> State)
    (xs ys : List Handler) (state : State) :
    run step (xs ++ ys) state = run step ys (run step xs state) := by
  induction xs generalizing state with
  | nil => rfl
  | cons h _ ih => exact ih (step h state)

inductive Reorders (step : Handler -> State -> State) : List Handler -> List Handler -> Prop
  | refl (trace) : Reorders step trace trace
  | swap (before after a b) (independent : Independent step a b) :
      Reorders step (before ++ a :: b :: after) (before ++ b :: a :: after)
  | trans {a b c} : Reorders step a b -> Reorders step b c -> Reorders step a c

theorem reordering_preserves_state (step : Handler -> State -> State)
    {first second : List Handler} (h : Reorders step first second) :
    forall state, run step first state = run step second state := by
  induction h with
  | refl => intro state; rfl
  | swap before after a b independent =>
      intro state
      simp only [run_append]
      exact independent_swap step a b independent after (run step before state)
  | trans _ _ ihFirst ihSecond =>
      intro state
      exact Eq.trans (ihFirst state) (ihSecond state)

#print axioms drain_safe
#print axioms drain_conservation
#print axioms admitted_available
#print axioms sync_preserves_tightening
#print axioms three_level_reduction
#print axioms reduction_steps_independent
#print axioms reordering_preserves_state

end Clockwork
