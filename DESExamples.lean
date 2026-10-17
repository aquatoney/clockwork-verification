import DES
import Examples

namespace Clockwork.Core.DES.Examples

def ownerOf (event : Nat) : Fin 2 :=
  if event = 1 ∨ event = 3 then ⟨1, by decide⟩ else ⟨0, by decide⟩

def increment (owner : Nat) : Handler Nat where
  access := ⟨owner, [owner], [owner]⟩
  step state key := if key = owner then state key + 1 else state key
  frame := by
    intro state key outside
    by_cases same : key = owner
    · subst key; exact False.elim (outside (.head []))
    · simp [same]
  locality := by
    intro before after equal key written
    cases written with
    | head => simp [equal owner (.head [])]
    | tail _ absent => cases absent

def emitted (event : Nat) : List Nat := if event = 1 then [3, 4] else []

def generated (event : Nat) (state : Store Nat) : List Nat :=
  if state (ownerOf event).val = 0 then emitted event else []

theorem emitted_later (event next : Nat) (member : List.Mem next (emitted event)) : event < next := by
  by_cases same : event = 1
  · subst event
    cases member with
    | head => decide
    | tail _ member =>
      cases member with
      | head => decide
      | tail _ absent => cases absent
  · simp only [emitted, if_neg same] at member; cases member

def model : Model Nat Nat 2 where
  time event := event + 1
  owner := ownerOf
  handler event := increment (ownerOf event).val
  emit := generated
  contribution event _ := event + 1
  algebra := Clockwork.Core.Examples.addition
  timeOrdered := by intro a b order; change a + 1 <= b + 1; omega
  successorsLater := by
    intro event state next member
    by_cases zero : state (ownerOf event).val = 0
    · exact emitted_later event next (by simpa [generated, zero] using member)
    · simp only [generated, if_neg zero] at member; cases member
  emitLocal := by
    intro event before after equal
    have same := equal (ownerOf event).val (.head [])
    simp only [generated, same]
  contributionLocal := by intros; rfl
  lookahead _ _ := 2
  delay := by
    intro event state next member _
    have enabled : state (ownerOf event).val = 0 := by
      by_cases zero : state (ownerOf event).val = 0
      · exact zero
      · simp only [generated, if_neg zero] at member; cases member
    have member : List.Mem next (emitted event) := by simpa [generated, enabled] using member
    by_cases same : event = 1
    · subst event
      cases member with
      | head => decide
      | tail _ member =>
        cases member with
        | head => decide
        | tail _ absent => cases absent
    · simp only [emitted, if_neg same] at member; cases member

def initial : State Nat Nat := ⟨fun _ => 0, fun event => if event = 0 ∨ event = 1 then 1 else 0, 0⟩
def afterLate : State Nat Nat := fire model 1 initial
def afterEarly : State Nat Nat := fire model 0 afterLate
def final : State Nat Nat := fire model 3 afterEarly

theorem initial_positive (event : Nat) : 0 < initial.pending event -> event = 0 ∨ event = 1 := by
  intro positive
  by_cases zero : event = 0
  · exact Or.inl zero
  · by_cases one : event = 1
    · exact Or.inr one
    · simp [initial, zero, one] at positive

theorem afterLate_positive (event : Nat) : 0 < afterLate.pending event -> event = 0 ∨ event = 3 ∨ event = 4 := by
  intro positive
  by_cases zero : event = 0
  · exact Or.inl zero
  · by_cases three : event = 3
    · exact Or.inr (Or.inl three)
    · by_cases four : event = 4
      · exact Or.inr (Or.inr four)
      · by_cases one : event = 1
        · subst event; contradiction
        · simp [afterLate, fire, initial, model, generated, emitted, countNode, zero, one, three, four,
            Ne.symm three, Ne.symm four] at positive

theorem afterEarly_positive (event : Nat) : 0 < afterEarly.pending event -> event = 3 ∨ event = 4 := by
  intro positive
  by_cases zero : event = 0
  · subst event; contradiction
  · have prior : 0 < afterLate.pending event := by
      simpa [afterEarly, fire, model, generated, emitted, zero, countNode] using positive
    rcases afterLate_positive event prior with same | same
    · exact False.elim (zero same)
    · exact same

def certificate₀ : ClockCertificate model initial where
  frontier _ := 0
  safe _ := 2
  closed := by intro event _; change (0 : Int) < (event : Int) + 1; omega
  forward := by intro _; change (0 : Int) <= 2; decide
  incoming := by intro _ _ _; change (2 : Int) <= 0 + 2; decide

theorem readyLate : Ready model 4 initial 1 := by constructor <;> decide
theorem enabledLate : ComposedEnabled model 4 initial 1 := by
  refine ⟨readyLate, ?_, certificate₀, by decide⟩
  intro other ready sameOwner
  rcases initial_positive other ready.1 with same | same
  · subst other; contradiction
  · subst other; exact Nat.le_refl _

def certificate₁ : ClockCertificate model afterLate :=
  certificate_after model initial 1 readyLate.1 certificate₀

theorem enabledEarly : ComposedEnabled model 4 afterLate 0 := by
  refine ⟨⟨by decide, by decide⟩, ?_, certificate₁, by decide⟩
  intro other _ _; exact Nat.zero_le _

def certificate₂ : ClockCertificate model afterEarly where
  frontier _ := 2
  safe _ := 4
  closed := by
    intro event positive
    rcases afterEarly_positive event positive with same | same
    · subst event; decide
    · subst event; decide
  forward := by intro _; change (2 : Int) <= 4; decide
  incoming := by intro _ _ _; change (4 : Int) <= 2 + 2; decide

theorem enabledSuccessor : ComposedEnabled model 4 afterEarly 3 := by
  refine ⟨⟨by decide, by decide⟩, ?_, certificate₂, by decide⟩
  intro other ready _
  rcases afterEarly_positive other ready.1 with same | same
  · subst other; exact Nat.le_refl _
  · subst other; exact False.elim (by have := ready.2; contradiction)

theorem composed : ComposedRun model 4 3 initial final :=
  Run.step enabledLate (Run.step enabledEarly (Run.step enabledSuccessor (.done _)))

theorem complete : Complete model 4 final := by
  intro event through
  have bound : event <= 3 := by change event + 1 <= 4 at through; omega
  have cases : event = 0 ∨ event = 1 ∨ event = 2 ∨ event = 3 := by omega
  rcases cases with same | same | same | same
  all_goals subst event; decide

def effects : List Access := [⟨0, [0], [0]⟩, ⟨1, [1], [1]⟩]
def plan : Plan := [[0], [1]]
def body : Code := .seq (.drain .effective) (.execute false effects)
def input : Code := .domain plan effects (.literal 99) body (.announceRoute (.literal 99)) []
def output : Code := normalize input
theorem accepted : compile [0, 1] input = some output := by decide

theorem coverage (event : Nat) : Within (model.handler event).access
    (accessAt effects (model.owner event).val) := by
  by_cases special : event = 1 ∨ event = 3
  · simp only [model, ownerOf, if_pos special, increment, effects, accessAt]
    exact ⟨fun _ member => member, fun _ member => member⟩
  · simp only [model, ownerOf, if_neg special, increment, effects, accessAt]
    exact ⟨fun _ member => member, fun _ member => member⟩

theorem independent : DomainIndependent model :=
  compiled_domain_independent [0, 1] input output accepted plan effects .effective body
    (.routeAnnounce .effective) [] .here model coverage

def binding : ProgramBinding [0, 1] plan body model where
  node event := (model.owner event).val
  known := by
    intro event
    by_cases special : event = 1 ∨ event = 3
    · change List.Mem (ownerOf event).val [0, 1]
      simp only [ownerOf, if_pos special]
      exact .tail 0 (.head [])
    · change List.Mem (ownerOf event).val [0, 1]
      simp only [ownerOf, if_neg special]
      exact .head _
  arity := rfl
  ownerMatches := by
    intro event
    by_cases special : event = 1 ∨ event = 3
    · simp [model, ownerOf, special, plan, locateOwner]
      decide
    · simp [model, ownerOf, special, plan, locateOwner]
  dispatcher := .prelude .effective (.execute effects)
  handlerDeclared := by
    intro event
    by_cases special : event = 1 ∨ event = 3
    · simp only [model, ownerOf, if_pos special, increment]
      exact .tail _ (.head [])
    · simp only [model, ownerOf, if_neg special, increment]
      exact .head _

theorem compiled_reference : ReferenceRun model 4 3 initial final :=
  (compiled_domain_design_reference [0, 1] input output accepted plan effects .effective body
    (.routeAnnounce .effective) [] .here model binding coverage 4 3 initial final
    (composed_run_effective model 4 3 initial final composed) complete).1

-- The theorem constructs reference semantics from a late-first composed run.
theorem reference : ReferenceRun model 4 3 initial final :=
  completed_run_reference model 4 independent 3 initial final composed complete

-- Independent execution of the reference order produces the same generated
-- successor and future event; no composed-trace sorting is used here.
def referenceFinal : State Nat Nat := fire model 3 (fire model 1 (fire model 0 initial))

theorem referenceInitial : ReferenceEnabled model 4 initial 0 :=
  ⟨⟨by decide, by decide⟩, fun _ _ => Nat.zero_le _⟩

theorem referenceSecond : ReferenceEnabled model 4 (fire model 0 initial) 1 := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro other ready
  by_cases zero : other = 0
  · subst other; exact False.elim (by have := ready.1; contradiction)
  · have prior : 0 < initial.pending other := by
      simpa [fire, model, generated, emitted, zero, countNode] using ready.1
    rcases initial_positive other prior with same | same
    · exact False.elim (zero same)
    · subst other; exact Nat.le_refl _

theorem swapped : fire model 1 (fire model 0 initial) = afterEarly :=
  fire_commutes model initial 0 1 (by decide) (by decide) (by decide)
    (independent 0 1 (by decide))

theorem referenceThird : ReferenceEnabled model 4 afterEarly 3 := by
  refine ⟨enabledSuccessor.1, ?_⟩
  intro other ready
  rcases afterEarly_positive other ready.1 with same | same
  · subst other; decide
  · subst other; decide

theorem independently_executed : ReferenceRun model 4 3 initial referenceFinal := by
  apply Run.step referenceInitial
  apply Run.step referenceSecond
  rw [swapped]
  change ReferenceRun model 4 1 afterEarly (fire model 3 (fire model 1 (fire model 0 initial)))
  rw [swapped]
  exact Run.step referenceThird (.done _)

theorem same_observations : final = referenceFinal := by
  have finished : Complete model 4 referenceFinal := by
    change Complete model 4 (fire model 3 (fire model 1 (fire model 0 initial)))
    rw [swapped]
    exact complete
  exact reference_unique model 4 3 3 initial final referenceFinal reference independently_executed complete finished

example : final.store 0 = 1 /\ final.store 1 = 2 /\ final.aggregate = 7 := by decide
example : final.pending 4 = 1 /\ final.pending 3 = 0 := by decide
example : generated 1 (fun _ => 0) = [3, 4] /\ generated 1 (fun _ => 1) = [] := by decide
example : referenceFinal.aggregate = 7 /\ referenceFinal.pending 4 = 1 := by decide
example : final.store = referenceFinal.store := by
  apply congrArg State.store
  have commute := fire_commutes model initial 1 0 (by decide) (by decide) (by decide)
    (independent 1 0 (by decide))
  exact congrArg (fire model 3) commute

def program : Program := ⟨4, .partition plan effects (.sequential 4 effects)⟩
def dslOutput : Executable := ⟨4, normalize (.loop (lower false program.body))⟩
theorem dslAccepted : compileProgram [0, 1] program = some dslOutput := by decide
def dslBinding : ProgramBinding [0, 1] plan (.execute false effects) model where
  toPlanBinding := binding.toPlanBinding
  dispatcher := .execute effects
  handlerDeclared := binding.handlerDeclared

example : ReferenceRun model program.horizon 3 initial final /\ dslOutput.horizon = program.horizon :=
  dsl_domain_design_reference [0, 1] program dslOutput dslAccepted plan effects .effective
    (.execute false effects) (.routeAnnounce .effective) [] (.loop .here) model dslBinding coverage
    3 initial final (composed_run_effective model 4 3 initial final composed) complete

-- Clock safety is not supplied as an assumed whole-trace order: without enough
-- lookahead, a lower producer prevents this particular late-first admission.
def zeroDelay : Model Nat Nat 2 := {model with
  lookahead := fun _ _ => 0,
  delay := by
    intro event state next member _
    have later := model.successorsLater event state next member
    change event + 1 + 0 <= next + 1
    omega }

example : ¬ ComposedEnabled zeroDelay 4 initial 1 := by
  intro enabled
  obtain ⟨certificate, bounded⟩ := enabled.2.2
  have closed := certificate.closed 0 (by decide)
  have incoming := certificate.incoming (zeroDelay.owner 0) (zeroDelay.owner 1) (by decide)
  change certificate.frontier (zeroDelay.owner 0) < (1 : Int) at closed
  change (certificate.safe (zeroDelay.owner 1) : Int) <= certificate.frontier (zeroDelay.owner 0) + 0 at incoming
  change 2 <= certificate.safe (zeroDelay.owner 1) at bounded
  omega

-- Negative initial frontiers permit a genuine event at timestamp zero.
def startsAtZero : Model Nat Nat 2 := {model with
  time := id,
  timeOrdered := fun _ _ order => order,
  delay := by
    intro event state next member different
    have delay := model.delay event state next member different
    change event + 1 + 2 <= next + 1 at delay
    change event + 2 <= next
    omega }

def beforeZero : ClockCertificate startsAtZero initial where
  frontier _ := -1
  safe _ := 1
  closed := by intro event _; change (-1 : Int) < (event : Int); omega
  forward := by intro _; change (-1 : Int) <= 1; decide
  incoming := by intro _ _ _; change (1 : Int) <= -1 + 2; decide

example : ComposedEnabled startsAtZero 0 initial 0 :=
  ⟨⟨by decide, by decide⟩, (fun _ _ _ => Nat.zero_le _), beforeZero, by decide⟩

end Clockwork.Core.DES.Examples
