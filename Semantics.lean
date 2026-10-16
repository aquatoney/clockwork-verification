import Core

namespace Clockwork.Core

abbrev Store (Value : Type) := Nat -> Value

-- A binding contract describes actual state effects, including reads used to
-- compute writes. These premises are independent of the conflict checker.
structure Handler (Value : Type) where
  access : Access
  step : Store Value -> Store Value
  frame : forall state key, (List.Mem key access.writes -> False) -> step state key = state key
  locality : forall before after,
    (forall key, List.Mem key access.reads -> before key = after key) ->
    forall key, List.Mem key access.writes -> step before key = step after key

theorem compatible_handlers_commute (a b : Handler Value)
    (compatible : Compatible a.access b.access) (state : Store Value) :
    b.step (a.step state) = a.step (b.step state) := by
  funext key
  by_cases writesA : List.Mem key a.access.writes
  case pos =>
    have outsideB : List.Mem key b.access.writes -> False :=
      fun writesB => compatible.1 key writesA writesB
    rw [b.frame (a.step state) key outsideB]
    have localEq := a.locality (b.step state) state
      (fun r hr => b.frame state r (fun hw => compatible.2.2 r hw hr)) key writesA
    exact localEq.symm
  case neg =>
    rw [a.frame (b.step state) key writesA]
    by_cases writesB : List.Mem key b.access.writes
    case pos =>
      exact b.locality (a.step state) state
        (fun r hr => a.frame state r (fun hw => compatible.2.1 r hw hr)) key writesB
    case neg =>
      rw [b.frame (a.step state) key writesB, a.frame state key writesA,
          b.frame state key writesB]

theorem checked_handlers_commute (a b : Handler Value)
    (accepted : accessCheck a.access b.access = true) :
    forall state, b.step (a.step state) = a.step (b.step state) :=
  compatible_handlers_commute a b (accessCheck_sound _ _ accepted)

-- Closed frontiers imply a delivery certificate under the declared lookahead.
structure Incoming where
  frontier : Nat
  lookahead : Nat
  deriving DecidableEq

def safeFrom (horizon : Nat) : List Incoming -> Nat
  | [] => horizon
  | edge :: rest => min (edge.frontier + edge.lookahead) (safeFrom horizon rest)

theorem safe_le_incoming (horizon : Nat) (edges : List Incoming)
    (edge : Incoming) (member : List.Mem edge edges) :
    safeFrom horizon edges <= edge.frontier + edge.lookahead := by
  induction member with
  | head rest => exact Nat.min_le_left _ _
  | tail other _ ih => exact Nat.le_trans (Nat.min_le_right _ _) ih

theorem unseen_after_safe (horizon : Nat) (edges : List Incoming) (edge : Incoming)
    (producer arrival : Nat) (member : List.Mem edge edges)
    (completed : edge.frontier < producer)
    (lookahead : producer + edge.lookahead <= arrival) :
    safeFrom horizon edges < arrival := by
  have bound := safe_le_incoming horizon edges edge member
  omega

theorem frontier_monotone (previous horizon : Nat) (edges : List Incoming)
    (horizonForward : previous <= horizon)
    (boundsForward : forall edge, List.Mem edge edges ->
      previous <= edge.frontier + edge.lookahead) :
    previous <= safeFrom horizon edges := by
  induction edges with
  | nil => exact horizonForward
  | cons edge rest ih =>
      apply Nat.le_min.mpr
      exact And.intro (boundsForward edge (.head rest))
        (ih (fun e he => boundsForward e (.tail edge he)))

-- An earliest *unprocessed* timestamp has the complementary strict rule.
theorem earliest_event_strict_bound (earliest producer lookahead arrival bound : Nat)
    (earliestKnown : earliest <= producer) (delay : producer + lookahead <= arrival)
    (strictBound : bound < earliest + lookahead) : bound < arrival := by omega

-- Inclusive admission also works at an earliest-event bound when delivery
-- assigns unseen equal-time events keys after the already admitted events.
theorem fifo_endpoint_safe (earliest producer lookahead arrival admitted : Nat)
    (incomingKey admittedKey : Nat)
    (earliestKnown : earliest <= producer)
    (delay : producer + lookahead <= arrival)
    (bounded : admitted <= earliest + lookahead)
    (tieOrder : arrival = admitted -> admittedKey < incomingKey) :
    (arrival < admitted \/ (arrival = admitted /\ incomingKey < admittedKey)) -> False := by
  intro precedes
  omega

theorem countNode_append (node : Nat) (xs ys : List Nat) :
    countNode node (xs ++ ys) = countNode node xs + countNode node ys := by
  induction xs with
  | nil => simp [countNode]
  | cons x xs ih => simp [countNode, ih, Nat.add_assoc]

theorem countNode_zero_of_absent (node : Nat) (xs : List Nat)
    (absent : List.Mem node xs -> False) : countNode node xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases eq : x = node
      case pos => subst x; exact False.elim (absent (.head xs))
      case neg =>
        simpa [countNode, eq] using ih (fun h => absent (.tail x h))

theorem ownership_preserves_nodes (nodes : List Nat) (oldPlan newPlan : Plan)
    (oldOwners : Owners nodes oldPlan) (newOwners : Owners nodes newPlan) :
    forall node, countNode node oldPlan.join = countNode node newPlan.join := by
  intro node
  by_cases member : List.Mem node nodes
  case pos => rw [oldOwners.1 node member, newOwners.1 node member]
  case neg =>
    rw [countNode_zero_of_absent node oldPlan.join (fun h => member (oldOwners.2 node h)),
        countNode_zero_of_absent node newPlan.join (fun h => member (newOwners.2 node h))]

def locateOwner (node : Nat) : Plan -> Option Nat
  | [] => none
  | domain :: rest =>
      if domain.contains node then some 0 else (locateOwner node rest).map Nat.succ

theorem member_append (item : Item) (xs ys : List Item)
    (member : List.Mem item (xs ++ ys)) : List.Mem item xs \/ List.Mem item ys := by
  induction xs with
  | nil => exact Or.inr member
  | cons x xs ih =>
      cases member with
      | head => exact Or.inl (.head xs)
      | tail _ member =>
          cases ih member with
          | inl hx => exact Or.inl (.tail x hx)
          | inr hy => exact Or.inr hy

theorem owner_exists (node : Nat) (plan : Plan) (member : List.Mem node plan.join) :
    exists owner, locateOwner node plan = some owner := by
  induction plan with
  | nil => cases member
  | cons domain rest ih =>
      by_cases here : domain.contains node = true
      case pos => exact Exists.intro 0 (by simp [locateOwner, here])
      case neg =>
        have inRest : List.Mem node rest.join := by
          have either := member_append node domain rest.join member
          cases either with
          | inl hd => exact False.elim (here (List.elem_eq_true_of_mem hd))
          | inr hr => exact hr
        cases ih inRest with
        | intro owner found =>
            exact Exists.intro (owner + 1) (by simp [locateOwner, here, found])

theorem checked_plan_has_owner (nodes : List Nat) (plan : Plan)
    (checked : planCheck nodes plan = true) (node : Nat) (known : List.Mem node nodes) :
    exists owner, locateOwner node plan = some owner := by
  have one := (planCheck_sound nodes plan checked).1 node known
  have member : List.Mem node plan.join := by
    by_cases h : List.Mem node plan.join
    case pos => exact h
    case neg => have zero := countNode_zero_of_absent node plan.join h; omega
  exact owner_exists node plan member

-- Routing carries each event intact to exactly one selected destination.
-- The existence theorem above ensures a checked plan supplies that owner.
structure Pending where
  node : Nat
  event : Clockwork.Event
  deriving DecidableEq

def route (owner : Nat -> Nat) (events : List Pending) : List (Prod Nat Pending) :=
  events.map (fun event => (owner event.node, event))

theorem routing_conserves_events (owner : Nat -> Nat) (events : List Pending) :
    (route owner events).map Prod.snd = events := by
  induction events with
  | nil => rfl
  | cons e rest ih => simp [route] at ih; simpa [route] using congrArg (List.cons e) ih

theorem migration_conserves_events (oldOwner newOwner : Nat -> Nat) (events : List Pending) :
    (route newOwner ((route oldOwner events).map Prod.snd)).map Prod.snd = events := by
  rw [routing_conserves_events, routing_conserves_events]

def select (admitted : Item -> Bool) : List Item -> List Item
  | [] => []
  | x :: rest => if admitted x then x :: select admitted rest else select admitted rest

def expand (transform : Item -> List Item) : List Item -> List Item
  | [] => []
  | x :: rest => transform x ++ expand transform rest

theorem select_append (admitted : Item -> Bool) (xs ys : List Item) :
    select admitted (xs ++ ys) = select admitted xs ++ select admitted ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases decision : admitted x <;> simp_all [select]

theorem select_uniform (admitted : Item -> Bool) (events : List Item) (bit : Bool)
    (uniform : forall e, List.Mem e events -> admitted e = bit) :
    select admitted events = if bit then events else [] := by
  induction events with
  | nil => cases bit <;> rfl
  | cons e rest ih =>
      have head := uniform e (.head rest)
      have tail := ih (fun x hx => uniform x (.tail e hx))
      cases bit <;> simp_all [select]

-- A pointwise ownership/time contract suffices to derive commutation with
-- admission. The conclusion is the rewrite law used by domain-entry repair.
theorem transform_admission (admitted : Item -> Bool) (transform : Item -> List Item)
    (preserves : forall e out, List.Mem out (transform e) -> admitted out = admitted e)
    (events : List Item) :
    select admitted (expand transform events) = expand transform (select admitted events) := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
      rw [expand, select_append, select_uniform admitted (transform e) (admitted e) (preserves e)]
      cases decision : admitted e <;> simp_all [select, expand]

def admission (owner : Nat -> Nat) (domain bound : Nat) (event : Pending) : Bool :=
  decide (owner event.node = domain /\ event.event.time <= bound)

theorem domain_entry_semantics (owner : Nat -> Nat) (domain bound : Nat)
    (transform : Pending -> List Pending)
    (preserves : forall e out, List.Mem out (transform e) ->
      owner out.node = owner e.node /\ out.event.time = e.event.time)
    (events : List Pending) :
    select (admission owner domain bound) (expand transform events) =
      expand transform (select (admission owner domain bound) events) := by
  apply transform_admission
  intro e out member
  have facts := preserves e out member
  simp only [admission, facts.1, facts.2]

#print axioms checked_handlers_commute
#print axioms unseen_after_safe
#print axioms frontier_monotone
#print axioms ownership_preserves_nodes
#print axioms checked_plan_has_owner
#print axioms migration_conserves_events
#print axioms domain_entry_semantics

end Clockwork.Core
