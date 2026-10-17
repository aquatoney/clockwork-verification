import Trace

namespace Clockwork.Core

-- A permutation preserves occurrences, not just membership. Kept here to avoid
-- adding a proof-library dependency to the pinned, bundled-only toolchain.
inductive Permutation : List Item -> List Item -> Prop
  | refl (items) : Permutation items items
  | cons (item) {before after} : Permutation before after ->
      Permutation (item :: before) (item :: after)
  | swap (a b) (rest) : Permutation (a :: b :: rest) (b :: a :: rest)
  | trans {a b c} : Permutation a b -> Permutation b c -> Permutation a c

theorem permutation_members {before after : List Item} (p : Permutation before after) :
    forall item, List.Mem item before <-> List.Mem item after := by
  induction p with
  | refl => intro item; rfl
  | cons head _ ih => intro item; simp only [member_cons, ih]
  | swap a b rest =>
    intro item
    simp only [member_cons]
    constructor <;> intro h <;> rcases h with h | h | h
    all_goals first | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr h)
  | trans _ _ ih₁ ih₂ => intro item; exact (ih₁ item).trans (ih₂ item)

theorem permutation_map (f : Item -> Other) {before after : List Item}
    (p : Permutation before after) : Permutation (before.map f) (after.map f) := by
  induction p with
  | refl => exact .refl _
  | cons item _ ih => exact .cons (f item) ih
  | swap a b rest => exact .swap (f a) (f b) (rest.map f)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem permutation_count (item : Access) {before after : List Access}
    (p : Permutation before after) :
    (before.filter (fun a => a == item)).length =
      (after.filter (fun a => a == item)).length := by
  induction p with
  | refl => rfl
  | cons head _ ih =>
    cases decision : head == item <;>
      simp only [List.filter, decision, List.length_cons]
    · exact ih
    · exact congrArg Nat.succ ih
  | swap a b rest =>
    cases ha : a == item <;> cases hb : b == item <;> simp [List.filter, ha, hb]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem compatible_symmetric (a b : Access) (safe : Compatible a b) : Compatible b a :=
  ⟨(fun key hb ha => safe.1 key ha hb), safe.2.2, safe.2.1⟩

theorem groupSafe_permutation {before after : List Access}
    (p : Permutation before after) : GroupSafe before -> GroupSafe after := by
  induction p with
  | refl => exact id
  | cons head p ih =>
    intro safe
    exact ⟨(fun other member => safe.1 other ((permutation_members p other).mpr member)), ih safe.2⟩
  | swap a b rest =>
    intro safe
    constructor
    · intro other member
      cases member with
      | head => exact compatible_symmetric a b (safe.1 b (.head rest))
      | tail _ member => exact safe.2.1 other member
    · exact ⟨(fun other member => safe.1 other (.tail b member)), safe.2.2⟩
  | trans _ _ ih₁ ih₂ => exact fun safe => ih₂ (ih₁ safe)

theorem mem_map (f : Item -> Other) (item : Item) (items : List Item)
    (member : List.Mem item items) : List.Mem (f item) (items.map f) := by
  induction member with
  | head rest => exact .head _
  | tail other _ ih => exact .tail _ ih

theorem groupSafe_conflictOrdered (actions : List (Action Value))
    (safe : GroupSafe (actions.map (fun a => a.handler.access))) :
    ConflictOrdered actions := by
  induction actions with
  | nil => trivial
  | cons action rest ih =>
    exact ⟨(fun later member _ => safe.1 later.handler.access
      (mem_map (fun a : Action Value => a.handler.access) later rest member)), ih safe.2⟩

theorem raceFree_site (code : Code) : RaceFree code ->
    forall group, List.Mem (true, group) (executionSites code) -> GroupSafe group := by
  induction code with
  | execute parallel declared =>
    intro safe group member
    rcases (member_cons _ _ _).mp member with same | absent
    · cases same; exact safe rfl
    · cases absent
  | seq a b iha ihb | branch g a b iha ihb =>
    intro safe group member
    cases member_append _ _ _ member with
    | inl ha => exact iha safe.1 group ha
    | inr hb => exact ihb safe.2 group hb
  | loop b ih => intro safe group member; exact ih safe group member
  | domain p e w b x t ih | entry f p e w b x t ih =>
    intro safe group member; exact ih safe.2 group member
  | _ => intro _ group member; cases member

theorem compiled_parallel_reference (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output)
    (group : List Access) (site : List.Mem (true, group) (executionSites output))
    (actions : List (Action Value))
    (realizes : Permutation group (actions.map (fun a => a.handler.access)))
    (state : Store Value) :
    runActions actions state = runActions (referenceOrder actions) state := by
  apply reference_equivalence
  apply groupSafe_conflictOrdered
  exact groupSafe_permutation realizes
    (raceFree_site output (pipeline_sound nodes input output accepted).i4 group site)

-- The boolean marks the occurrence's lexical spatial context. Include the
-- implicit admission prelude of every domain, even at an outer root.
def admissionSites (inside : Bool) : Code -> List (Prod Bool Bound)
  | .drain bound => [(inside, bound)]
  | .seq a b | .branch _ a b => admissionSites inside a ++ admissionSites inside b
  | .loop body => admissionSites inside body
  | .domain _ _ bound body _ _ | .entry _ _ _ bound body _ _ =>
      (true, bound) :: admissionSites true body
  | _ => []

theorem bounded_admission (code : Code) (inside : Bool) (bounded : Bounded inside code) :
    forall bound, List.Mem (true, bound) (admissionSites inside code) -> bound = .effective := by
  induction code generalizing inside with
  | drain declared =>
    intro bound member
    rcases (member_cons _ _ _).mp member with same | absent
    · cases same; exact bounded rfl
    · cases absent
  | seq a b iha ihb | branch g a b iha ihb =>
    intro bound member
    cases member_append _ _ _ member with
    | inl ha => exact iha inside bounded.1 bound ha
    | inr hb => exact ihb inside bounded.2 bound hb
  | loop b ih => exact ih inside bounded
  | domain p e w b x t ih | entry f p e w b x t ih =>
    intro bound member
    rcases (member_cons _ _ _).mp member with same | member
    · cases same; exact bounded.1
    · exact ih true bounded.2 bound member
  | _ => intro bound member; cases member

def evalBound (window safe : Nat) : Bound -> Nat
  | .literal time => time
  | .effective => Clockwork.effective window safe

theorem bounded_drain_safe (code : Code) (bound : Bound)
    (inside : Bool) (bounded : Bounded inside code)
    (site : List.Mem (true, bound) (admissionSites inside code))
    (window safe : Nat) (events : List Clockwork.Event) :
    Clockwork.allThrough safe (Clockwork.drain (evalBound window safe bound) events).1 := by
  rw [bounded_admission code inside bounded bound site]
  exact Clockwork.drain_safe window safe events

-- A genuine delivery result: combine IR bound resolution with the closed
-- frontier / lookahead contract, rather than postulating availability itself.
theorem bounded_admission_no_unseen_predecessor (code : Code) (bound : Bound)
    (inside : Bool) (bounded : Bounded inside code)
    (site : List.Mem (true, bound) (admissionSites inside code))
    (window horizon : Nat) (edges : List Incoming) (events : List Clockwork.Event)
    (admitted : Clockwork.Event)
    (member : List.Mem admitted
      (Clockwork.drain (evalBound window (safeFrom horizon edges) bound) events).1)
    (edge : Incoming) (incoming : List.Mem edge edges) (producer arrival : Nat)
    (completed : edge.frontier < producer)
    (delay : producer + edge.lookahead <= arrival) : admitted.time < arrival := by
  have through := bounded_drain_safe code bound inside bounded site window (safeFrom horizon edges) events
  have eventBound : admitted.time <= safeFrom horizon edges := by
    generalize (Clockwork.drain (evalBound window (safeFrom horizon edges) bound) events).1 = es at *
    induction member with
    | head => exact through.1
    | tail other _ ih => exact ih through.2
  exact Nat.lt_of_le_of_lt eventBound
    (unseen_after_safe horizon edges edge producer arrival incoming completed delay)

theorem compiled_drain_safe (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (bound : Bound)
    (site : List.Mem (true, bound) (admissionSites false output))
    (window safe : Nat) (events : List Clockwork.Event) :
    Clockwork.allThrough safe (Clockwork.drain (evalBound window safe bound) events).1 :=
  bounded_drain_safe output bound false (pipeline_sound nodes input output accepted).i1.1
    site window safe events

theorem compiled_admission_no_unseen_predecessor (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (bound : Bound)
    (site : List.Mem (true, bound) (admissionSites false output))
    (window horizon : Nat) (edges : List Incoming) (events : List Clockwork.Event)
    (admitted : Clockwork.Event)
    (member : List.Mem admitted
      (Clockwork.drain (evalBound window (safeFrom horizon edges) bound) events).1)
    (edge : Incoming) (incoming : List.Mem edge edges) (producer arrival : Nat)
    (completed : edge.frontier < producer)
    (delay : producer + edge.lookahead <= arrival) : admitted.time < arrival :=
  bounded_admission_no_unseen_predecessor output bound false
    (pipeline_sound nodes input output accepted).i1.1 site window horizon edges events
    admitted member edge incoming producer arrival completed delay

-- Recursive containment, used to connect compiled domain nodes to their
-- boundary, reduction and ownership consequences without a flat IR surrogate.
inductive Subcode (child : Code) : Code -> Prop
  | here : Subcode child child
  | left {a b} : Subcode child a -> Subcode child (.seq a b)
  | right {a b} : Subcode child b -> Subcode child (.seq a b)
  | yes {g a b} : Subcode child a -> Subcode child (.branch g a b)
  | no {g a b} : Subcode child b -> Subcode child (.branch g a b)
  | loop {body} : Subcode child body -> Subcode child (.loop body)
  | domain {p e w body x t} : Subcode child body -> Subcode child (.domain p e w body x t)
  | entry {f p e w body x t} : Subcode child body -> Subcode child (.entry f p e w body x t)

theorem ordered_subcode {child code : Code} (site : Subcode child code) : Ordered code -> Ordered child := by
  induction site with
  | here => exact id
  | left _ ih | yes _ ih => exact fun h => ih h.1
  | right _ ih | no _ ih | domain _ ih | entry _ ih => exact fun h => ih h.2
  | loop _ ih => exact ih

theorem conserved_subcode (nodes : List Nat) {child code : Code} (site : Subcode child code) :
    Conserved nodes code -> Conserved nodes child := by
  induction site with
  | here => exact id
  | left _ ih | yes _ ih => exact fun h => ih h.1
  | right _ ih | no _ ih | domain _ ih | entry _ ih => exact fun h => ih h.2
  | loop _ ih => exact ih

theorem reduced_domain {p e w body x tail code}
    (site : Subcode (.domain p e w body x tail) code) (inside : Bool)
    (reduced : Reduced inside code) : Reduced true body /\ tail = requiredTail body := by
  induction site generalizing inside with
  | here => exact reduced
  | left _ ih | yes _ ih => exact ih inside reduced.1
  | right _ ih | no _ ih => exact ih inside reduced.2
  | loop _ ih => exact ih inside reduced
  | domain _ ih | entry _ ih => exact ih true reduced.1

theorem compiled_domain_contract (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) (p e w body boundary tail)
    (site : Subcode (.domain p e w body boundary tail) output) :
    boundary = .routeAnnounce .effective /\ tail = requiredTail body /\ Owners nodes p := by
  have invariant := pipeline_sound nodes input output accepted
  exact ⟨(ordered_subcode site invariant.i3).1,
    (reduced_domain site false invariant.i2).2,
    (conserved_subcode nodes site invariant.i5).1⟩

theorem owners_have_owner (nodes : List Nat) (plan : Plan) (owners : Owners nodes plan)
    (node : Nat) (known : List.Mem node nodes) :
    exists owner, locateOwner node plan = some owner := by
  have one := owners.1 node known
  have member : List.Mem node plan.join := by
    by_cases member : List.Mem node plan.join
    · exact member
    · have zero := countNode_zero_of_absent node plan.join member; omega
  exact owner_exists node plan member

#print axioms compiled_parallel_reference
#print axioms bounded_admission_no_unseen_predecessor
#print axioms compiled_admission_no_unseen_predecessor
#print axioms compiled_domain_contract

end Clockwork.Core
