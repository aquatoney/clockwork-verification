import Semantics

namespace Clockwork.Core

-- priority encodes the reference timestamp/tie order for a finite completed
-- trace. The handler contract includes every state region it reads or writes.
structure Action (Value : Type) where
  priority : Nat
  handler : Handler Value

def runActions (actions : List (Action Value)) (state : Store Value) : Store Value :=
  Clockwork.run (fun action => action.handler.step) actions state

def insertAction (action : Action Value) : List (Action Value) -> List (Action Value)
  | [] => [action]
  | next :: rest =>
      if action.priority <= next.priority then action :: next :: rest
      else next :: insertAction action rest

def referenceOrder : List (Action Value) -> List (Action Value)
  | [] => []
  | action :: rest => insertAction action (referenceOrder rest)

theorem member_cons (item head : Item) (rest : List Item) :
    List.Mem item (head :: rest) <-> item = head \/ List.Mem item rest := by
  constructor
  case mp =>
    intro h
    cases h with
    | head => exact Or.inl rfl
    | tail _ h => exact Or.inr h
  case mpr =>
    intro h
    cases h with
    | inl same => subst item; exact .head rest
    | inr h => exact .tail head h

theorem insert_members (item action : Action Value) (rest : List (Action Value)) :
    List.Mem item (insertAction action rest) <-> item = action \/ List.Mem item rest := by
  induction rest with
  | nil =>
      simp only [insertAction, member_cons]
  | cons next rest ih =>
      by_cases before : action.priority <= next.priority
      case pos => simp only [insertAction, if_pos before, member_cons]
      case neg =>
        simp only [insertAction, if_neg before, member_cons, ih]
        constructor <;> intro h <;> rcases h with h | h | h
        all_goals first | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr h)

theorem reference_members (item : Action Value) (actions : List (Action Value)) :
    List.Mem item (referenceOrder actions) <-> List.Mem item actions := by
  induction actions with
  | nil => rfl
  | cons action rest ih => simp only [referenceOrder, insert_members, member_cons, ih]

-- A trace may invert the reference order only for independent handlers.
def ConflictOrdered : List (Action Value) -> Prop
  | [] => True
  | action :: rest =>
      (forall later, List.Mem later rest -> later.priority < action.priority ->
        Compatible action.handler.access later.handler.access) /\ ConflictOrdered rest

theorem insertion_preserves_state (action : Action Value) (actions : List (Action Value))
    (compatible : forall other, List.Mem other actions -> other.priority < action.priority ->
      Compatible action.handler.access other.handler.access) :
    forall state, runActions (insertAction action actions) state =
      runActions (action :: actions) state := by
  induction actions with
  | nil => intro state; rfl
  | cons next rest ih =>
      intro state
      by_cases before : action.priority <= next.priority
      case pos => simp [insertAction, before]
      case neg =>
        have commute := compatible_handlers_commute action.handler next.handler
          (compatible next (.head rest) (by omega)) state
        simp only [insertAction, if_neg before]
        change runActions (insertAction action rest) (next.handler.step state) =
          runActions rest (next.handler.step (action.handler.step state))
        rw [ih (fun other h order => compatible other (.tail next h) order)
          (next.handler.step state)]
        exact congrArg (runActions rest) commute.symm

theorem sorted_execution (actions : List (Action Value)) (ordered : ConflictOrdered actions) :
    forall state, runActions (referenceOrder actions) state = runActions actions state := by
  induction actions with
  | nil => intro state; rfl
  | cons action rest ih =>
      intro state
      change runActions (insertAction action (referenceOrder rest)) state =
        runActions rest (action.handler.step state)
      rw [insertion_preserves_state action (referenceOrder rest)
        (fun other h order => ordered.1 other ((reference_members other rest).mp h) order) state]
      exact ih ordered.2 (action.handler.step state)

theorem reference_equivalence (actions : List (Action Value))
    (ordered : ConflictOrdered actions) (state : Store Value) :
    runActions actions state = runActions (referenceOrder actions) state :=
  (sorted_execution actions ordered state).symm

def PrioritySorted : List (Action Value) -> Prop
  | [] => True
  | action :: rest =>
      (forall later, List.Mem later rest -> action.priority <= later.priority) /\ PrioritySorted rest

theorem insertion_sorted (action : Action Value) (actions : List (Action Value))
    (sorted : PrioritySorted actions) : PrioritySorted (insertAction action actions) := by
  induction actions with
  | nil =>
      constructor
      case left => intro later member; cases member
      case right => trivial
  | cons next rest ih =>
      by_cases before : action.priority <= next.priority
      case pos =>
        simp only [insertAction, if_pos before, PrioritySorted]
        refine And.intro ?_ sorted
        intro later member
        cases member with
        | head => exact before
        | tail _ h => exact Nat.le_trans before (sorted.1 later h)
      case neg =>
        simp only [insertAction, if_neg before, PrioritySorted]
        refine And.intro ?_ (ih sorted.2)
        intro later member
        cases (insert_members later action rest).mp member with
        | inl same => subst later; omega
        | inr h => exact sorted.1 later h

theorem reference_sorted (actions : List (Action Value)) : PrioritySorted (referenceOrder actions) := by
  induction actions with
  | nil => trivial
  | cons action rest ih => exact insertion_sorted action (referenceOrder rest) ih

#print axioms reference_equivalence
#print axioms reference_sorted

end Clockwork.Core
