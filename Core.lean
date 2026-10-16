import Clockwork

namespace Clockwork.Core

-- Resource names below are resolved state-region/key pairs from the binding.
structure Access where
  handler : Nat := 0
  reads : List Nat
  writes : List Nat
  deriving DecidableEq, Repr

def every (test : Item -> Bool) : List Item -> Bool
  | [] => true
  | x :: xs => test x && every test xs

theorem every_iff (test : Item -> Bool) (xs : List Item) :
    every test xs = true <-> forall x, List.Mem x xs -> test x = true := by
  induction xs with
  | nil =>
      constructor
      case mp => intro _ x hx; cases hx
      case mpr => intro _; rfl
  | cons x xs ih =>
      constructor
      case mp =>
        intro h y hy
        have parts : test x = true /\ every test xs = true := by
          simpa only [every, Bool.and_eq_true] using h
        cases hy with
        | head => exact parts.1
        | tail _ hy => exact ih.mp parts.2 y hy
      case mpr =>
        intro h
        simp only [every, Bool.and_eq_true]
        exact And.intro (h x (.head xs)) (ih.mpr (fun y hy => h y (.tail x hy)))

def disjointCheck (xs ys : List Nat) : Bool :=
  every (fun x => !ys.contains x) xs

def Disjoint (xs ys : List Nat) : Prop :=
  forall x, List.Mem x xs -> List.Mem x ys -> False

theorem disjointCheck_sound (xs ys : List Nat) (h : disjointCheck xs ys = true) :
    Disjoint xs ys := by
  intro x hx hy
  have checked := (every_iff _ xs).mp h x hx
  have contained := List.elem_eq_true_of_mem hy
  simp [List.contains, contained] at checked

def accessCheck (a b : Access) : Bool :=
  disjointCheck a.writes b.writes &&
  disjointCheck a.writes b.reads && disjointCheck b.writes a.reads

def Compatible (a b : Access) : Prop :=
  Disjoint a.writes b.writes /\
  Disjoint a.writes b.reads /\ Disjoint b.writes a.reads

theorem accessCheck_sound (a b : Access) (h : accessCheck a b = true) :
    Compatible a b := by
  simp only [accessCheck, Bool.and_eq_true] at h
  exact And.intro (disjointCheck_sound _ _ h.1.1)
    (And.intro (disjointCheck_sound _ _ h.1.2) (disjointCheck_sound _ _ h.2))

def groupCheck : List Access -> Bool
  | [] => true
  | a :: rest => every (accessCheck a) rest && groupCheck rest

def GroupSafe : List Access -> Prop
  | [] => True
  | a :: rest => (forall b, List.Mem b rest -> Compatible a b) /\ GroupSafe rest

theorem groupCheck_sound (group : List Access) (h : groupCheck group = true) :
    GroupSafe group := by
  induction group with
  | nil => trivial
  | cons a rest ih =>
      simp only [groupCheck, Bool.and_eq_true] at h
      exact And.intro (fun b hb => accessCheck_sound a b ((every_iff _ _).mp h.1 b hb))
        (ih h.2)

abbrev Plan := List (List Nat)

def countNode (node : Nat) : List Nat -> Nat
  | [] => 0
  | n :: rest => (if n = node then 1 else 0) + countNode node rest

-- Check each binding node has exactly one owner and every owned node is known.
def planCheck (nodes : List Nat) (plan : Plan) : Bool :=
  every (fun n => decide (countNode n plan.join = 1)) nodes &&
  every (fun n => nodes.contains n) plan.join

def Owners (nodes : List Nat) (plan : Plan) : Prop :=
  (forall n, List.Mem n nodes -> countNode n plan.join = 1) /\
  (forall n, List.Mem n plan.join -> List.Mem n nodes)

theorem planCheck_sound (nodes : List Nat) (plan : Plan)
    (h : planCheck nodes plan = true) : Owners nodes plan := by
  simp only [planCheck, Bool.and_eq_true] at h
  constructor
  case left =>
    intro n hn
    exact of_decide_eq_true ((every_iff _ _).mp h.1 n hn)
  case right =>
    intro n hn
    exact List.mem_of_elem_eq_true ((every_iff _ _).mp h.2 n hn)

structure Transform where
  name : Nat
  domainPreserving : Bool
  deriving DecidableEq, Repr

inductive Boundary where
  | announceRoute (time : Bound)
  | routeAnnounce (time : Bound)
  deriving DecidableEq

inductive TailOp where
  | barrier
  | globalReduce (region : Nat)
  deriving DecidableEq, Repr

-- A domain node abbreviates ComputeSafeTime/MinBound, its admission Drain,
-- ForEachDomain body and boundary, followed by the epilogue OUTSIDE that loop.
-- reducePair abbreviates adjacent Reduce(BatchLocal)/Reduce(PartitionLocal).
inductive Code where
  | stop
  | invalid
  | drain (bound : Bound)
  | execute (parallel : Bool) (group : List Access)
  | transform (fn : Transform)
  | reduceBatch (region : Nat)
  | reducePair (region : Nat)
  | seq (first second : Code)
  | loop (body : Code)
  | branch (guard : Nat) (yes no : Code)
  | domain (plan : Plan) (crossEffects : List Access) (admission : Bound)
      (body : Code) (boundary : Boundary) (epilogue : List TailOp)
  | entry (fn : Transform) (plan : Plan) (crossEffects : List Access)
      (admission : Bound) (body : Code) (boundary : Boundary) (epilogue : List TailOp)
  | reassign (plan : Plan)
  deriving DecidableEq

-- Each traversal retains all data, declarations, guards, and domain plans.
def entryPass : Code -> Code
  | .seq a b => .seq (entryPass a) (entryPass b)
  | .loop b => .loop (entryPass b)
  | .branch g a b => .branch g (entryPass a) (entryPass b)
  | .domain p e w b x t => .domain p e w (entryPass b) x t
  | .entry f p e w b x t =>
      if f.domainPreserving then
        .domain p e .effective (.seq (.transform f) (entryPass b)) x t
      else .entry f p e w (entryPass b) x t
  | other => other

def boundPass (inside : Bool) : Code -> Code
  | .drain b => .drain (if inside then retarget b else b)
  | .seq a b => .seq (boundPass inside a) (boundPass inside b)
  | .loop b => .loop (boundPass inside b)
  | .branch g a b => .branch g (boundPass inside a) (boundPass inside b)
  | .domain p e w b x t => .domain p e (retarget w) (boundPass true b) x t
  | .entry f p e w b x t => .entry f p e (retarget w) (boundPass true b) x t
  | other => other

def fixBoundary : Boundary -> Boundary
  | .announceRoute b => .routeAnnounce (retarget b)
  | .routeAnnounce b => .routeAnnounce (retarget b)

def syncPass : Code -> Code
  | .seq a b => .seq (syncPass a) (syncPass b)
  | .loop b => .loop (syncPass b)
  | .branch g a b => .branch g (syncPass a) (syncPass b)
  | .domain p e w b x t => .domain p e w (syncPass b) (fixBoundary x) t
  | .entry f p e w b x t => .entry f p e w (syncPass b) (fixBoundary x) t
  | other => other

-- Collect regions at the current spatial scope; nested domains have their
-- own epilogues. Repeated references name one global accumulator.
def regions : Code -> List Nat
  | .reduceBatch r | .reducePair r => [r]
  | .seq a b | .branch _ a b => regions a ++ regions b
  | .loop b => regions b
  | _ => []

def uniqueRegions (xs : List Nat) : List Nat := xs.eraseDups

def requiredTail (body : Code) : List TailOp :=
  match uniqueRegions (regions body) with
  | [] => []
  | rs => .barrier :: rs.map TailOp.globalReduce

def reductionPass (inside : Bool) : Code -> Code
  | .reduceBatch r => if inside then .reducePair r else .reduceBatch r
  | .seq a b => .seq (reductionPass inside a) (reductionPass inside b)
  | .loop b => .loop (reductionPass inside b)
  | .branch g a b => .branch g (reductionPass inside a) (reductionPass inside b)
  | .domain p e w b x _ =>
      let fixed := reductionPass true b
      .domain p e w fixed x (requiredTail fixed)
  | .entry f p e w b x _ =>
      let fixed := reductionPass true b
      .entry f p e w fixed x (requiredTail fixed)
  | other => other

-- The five IR obligations are propositions independent of the compiler.
def Bounded (inside : Bool) : Code -> Prop
  | .drain b => inside = true -> b = .effective
  | .seq a b | .branch _ a b => Bounded inside a /\ Bounded inside b
  | .loop b => Bounded inside b
  | .domain _ _ w b _ _ | .entry _ _ _ w b _ _ =>
      w = .effective /\ Bounded true b
  | _ => True

def Reduced (inside : Bool) : Code -> Prop
  | .reduceBatch _ => inside = false
  | .seq a b | .branch _ a b => Reduced inside a /\ Reduced inside b
  | .loop b => Reduced inside b
  | .domain _ _ _ b _ t | .entry _ _ _ _ b _ t =>
      Reduced true b /\ t = requiredTail b
  | _ => True

def Ordered : Code -> Prop
  | .seq a b | .branch _ a b => Ordered a /\ Ordered b
  | .loop b => Ordered b
  | .domain _ _ _ b x _ | .entry _ _ _ _ b x _ =>
      x = .routeAnnounce .effective /\ Ordered b
  | _ => True

def RaceFree : Code -> Prop
  | .execute parallel group => parallel = true -> GroupSafe group
  | .seq a b | .branch _ a b => RaceFree a /\ RaceFree b
  | .loop b => RaceFree b
  | .domain _ e _ b _ _ | .entry _ _ e _ b _ _ => GroupSafe e /\ RaceFree b
  | _ => True

def Conserved (nodes : List Nat) : Code -> Prop
  | .seq a b | .branch _ a b => Conserved nodes a /\ Conserved nodes b
  | .loop b => Conserved nodes b
  | .domain p _ _ b _ _ | .entry _ p _ _ b _ _ =>
      Owners nodes p /\ Conserved nodes b
  | .reassign p => Owners nodes p
  | _ => True

def EntryLegal : Code -> Prop
  | .invalid | .entry _ _ _ _ _ _ _ => False
  | .seq a b | .branch _ a b => EntryLegal a /\ EntryLegal b
  | .loop b | .domain _ _ _ b _ _ => EntryLegal b
  | _ => True

-- Validation checks the facts that rewriting cannot manufacture. It does
-- not test Bounded, Reduced or Ordered; the pass proofs establish those.
def validate (nodes : List Nat) : Code -> Bool
  | .invalid | .entry _ _ _ _ _ _ _ => false
  | .execute parallel group => if parallel then groupCheck group else true
  | .seq a b | .branch _ a b => validate nodes a && validate nodes b
  | .loop b => validate nodes b
  | .domain p e _ b _ _ => planCheck nodes p && groupCheck e && validate nodes b
  | .reassign p => planCheck nodes p
  | _ => true

def normalize (code : Code) : Code :=
  reductionPass false (syncPass (boundPass false (entryPass code)))

def compile (nodes : List Nat) (code : Code) : Option Code :=
  let normalized := normalize code
  if validate nodes normalized then some normalized else none

structure Invariants (nodes : List Nat) (code : Code) : Prop where
  i1 : Bounded false code /\ EntryLegal code
  i2 : Reduced false code
  i3 : Ordered code
  i4 : RaceFree code
  i5 : Conserved nodes code

theorem bound_establishes (code : Code) (inside : Bool) :
    Bounded inside (boundPass inside code) := by
  induction code generalizing inside <;>
    simp_all [boundPass, Bounded, retarget_effective]

theorem sync_establishes (code : Code) : Ordered (syncPass code) := by
  have fixed : forall b, fixBoundary b = .routeAnnounce .effective := by
    intro b; cases b <;> simp [fixBoundary]
  induction code <;> simp_all [syncPass, Ordered, fixed]

theorem reduction_establishes (code : Code) (inside : Bool) :
    Reduced inside (reductionPass inside code) := by
  induction code generalizing inside <;>
    simp_all [reductionPass, Reduced]
  case reduceBatch r => cases inside <;> trivial

theorem sync_preserves_bounded (code : Code) (inside : Bool) :
    Bounded inside (syncPass code) <-> Bounded inside code := by
  induction code generalizing inside <;> simp_all [syncPass, Bounded]

theorem reduction_preserves_bounded (code : Code) (inside active : Bool) :
    Bounded inside (reductionPass active code) <-> Bounded inside code := by
  induction code generalizing inside active <;>
    simp_all [reductionPass, Bounded]
  case reduceBatch r => cases active <;> trivial

theorem reduction_preserves_ordered (code : Code) (inside : Bool) :
    Ordered (reductionPass inside code) <-> Ordered code := by
  induction code generalizing inside <;> simp_all [reductionPass, Ordered]
  case reduceBatch r => cases inside <;> trivial

theorem validation_sound (nodes : List Nat) (code : Code)
    (accepted : validate nodes code = true) :
    EntryLegal code /\ RaceFree code /\ Conserved nodes code := by
  induction code with
  | execute parallel group =>
      cases parallel <;> simp_all [validate, EntryLegal, RaceFree, Conserved, groupCheck_sound]
  | domain p e w body x tail ih =>
      simp only [validate, Bool.and_eq_true] at accepted
      have child := ih accepted.2
      exact And.intro child.1 (And.intro
        (And.intro (groupCheck_sound e accepted.1.2) child.2.1)
        (And.intro (planCheck_sound nodes p accepted.1.1) child.2.2))
  | reassign p =>
      exact And.intro trivial (And.intro trivial (planCheck_sound _ _ accepted))
  | _ => simp_all [validate, EntryLegal, RaceFree, Conserved, Bool.and_eq_true]

theorem pipeline_sound (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) : Invariants nodes output := by
  dsimp only [compile] at accepted
  split at accepted
  case inl checked =>
    have outputEq : normalize input = output := Option.some.inj accepted
    subst output
    have checks := validation_sound nodes (normalize input) checked
    constructor
    case i1 =>
      refine And.intro ?_ checks.1
      unfold normalize
      apply (reduction_preserves_bounded _ _ _).mpr
      apply (sync_preserves_bounded _ _).mpr
      exact bound_establishes _ _
    case i2 => exact reduction_establishes _ _
    case i3 =>
      apply (reduction_preserves_ordered _ _).mpr
      exact sync_establishes _
    case i4 => exact checks.2.1
    case i5 => exact checks.2.2
  case inr rejected => contradiction

theorem entry_preserves_races (code : Code) :
    RaceFree (entryPass code) <-> RaceFree code := by
  induction code <;> simp_all [entryPass, RaceFree]
  case entry f p e w b x t ih => cases f.domainPreserving <;> simp_all [RaceFree]

theorem entry_preserves_owners (nodes : List Nat) (code : Code) :
    Conserved nodes (entryPass code) <-> Conserved nodes code := by
  induction code <;> simp_all [entryPass, Conserved]
  case entry f p e w b x t ih => cases f.domainPreserving <;> simp_all [Conserved]

theorem bound_preserves_races (code : Code) (inside : Bool) :
    RaceFree (boundPass inside code) <-> RaceFree code := by
  induction code generalizing inside <;> simp_all [boundPass, RaceFree]

theorem bound_preserves_owners (nodes : List Nat) (code : Code) (inside : Bool) :
    Conserved nodes (boundPass inside code) <-> Conserved nodes code := by
  induction code generalizing inside <;> simp_all [boundPass, Conserved]

theorem sync_preserves_races (code : Code) :
    RaceFree (syncPass code) <-> RaceFree code := by
  induction code <;> simp_all [syncPass, RaceFree]

theorem sync_preserves_owners (nodes : List Nat) (code : Code) :
    Conserved nodes (syncPass code) <-> Conserved nodes code := by
  induction code <;> simp_all [syncPass, Conserved]

theorem reduction_preserves_races (code : Code) (inside : Bool) :
    RaceFree (reductionPass inside code) <-> RaceFree code := by
  induction code generalizing inside <;> simp_all [reductionPass, RaceFree]
  case reduceBatch r => cases inside <;> trivial

theorem reduction_preserves_owners (nodes : List Nat) (code : Code) (inside : Bool) :
    Conserved nodes (reductionPass inside code) <-> Conserved nodes code := by
  induction code generalizing inside <;> simp_all [reductionPass, Conserved]
  case reduceBatch r => cases inside <;> trivial

theorem entry_fixed (code : Code) (h : EntryLegal code) : entryPass code = code := by
  induction code <;> simp_all [EntryLegal, entryPass]

theorem bound_fixed (code : Code) (inside : Bool) (h : Bounded inside code) :
    boundPass inside code = code := by
  induction code generalizing inside <;> simp_all [Bounded, boundPass]

theorem sync_fixed (code : Code) (h : Ordered code) : syncPass code = code := by
  induction code <;> simp_all [Ordered, syncPass, fixBoundary]

theorem reduction_fixed (code : Code) (inside : Bool) (h : Reduced inside code) :
    reductionPass inside code = code := by
  induction code generalizing inside <;> simp_all [Reduced, reductionPass]

theorem accepted_normal_form (nodes : List Nat) (input output : Code)
    (accepted : compile nodes input = some output) : normalize output = output := by
  have inv := pipeline_sound nodes input output accepted
  unfold normalize
  rw [entry_fixed output inv.i1.2, bound_fixed output false inv.i1.1,
      sync_fixed output inv.i3, reduction_fixed output false inv.i2]

def EntryAdmissible : Code -> Prop
  | .invalid => False
  | .entry f _ _ _ b _ _ => f.domainPreserving = true /\ EntryAdmissible b
  | .seq a b | .branch _ a b => EntryAdmissible a /\ EntryAdmissible b
  | .loop b | .domain _ _ _ b _ _ => EntryAdmissible b
  | _ => True

theorem entry_establishes (code : Code) (admissible : EntryAdmissible code) :
    EntryLegal (entryPass code) := by
  induction code <;> simp_all [EntryAdmissible, entryPass, EntryLegal]

theorem bound_preserves_entry (code : Code) (inside : Bool) :
    EntryLegal (boundPass inside code) <-> EntryLegal code := by
  induction code generalizing inside <;> simp_all [boundPass, EntryLegal]

theorem sync_preserves_entry (code : Code) :
    EntryLegal (syncPass code) <-> EntryLegal code := by
  induction code <;> simp_all [syncPass, EntryLegal]

theorem reduction_preserves_entry (code : Code) (inside : Bool) :
    EntryLegal (reductionPass inside code) <-> EntryLegal code := by
  induction code generalizing inside <;> simp_all [reductionPass, EntryLegal]
  case reduceBatch r => cases inside <;> trivial

theorem reduction_preserves_regions (code : Code) (inside : Bool) :
    regions (reductionPass inside code) = regions code := by
  induction code generalizing inside <;> simp_all [reductionPass, regions]
  case reduceBatch r => cases inside <;> rfl

-- Later passes retain the executable sites, including sites in both arms.
def executionSites : Code -> List (Prod Bool (List Access))
  | .execute parallel group => [(parallel, group)]
  | .seq a b | .branch _ a b => executionSites a ++ executionSites b
  | .loop b | .domain _ _ _ b _ _ | .entry _ _ _ _ b _ _ => executionSites b
  | _ => []

theorem entry_preserves_sites (code : Code) :
    executionSites (entryPass code) = executionSites code := by
  induction code <;> simp_all [entryPass, executionSites]
  case entry f p e w b x t ih => cases f.domainPreserving <;> simp_all [executionSites]

theorem bound_preserves_sites (code : Code) (inside : Bool) :
    executionSites (boundPass inside code) = executionSites code := by
  induction code generalizing inside <;> simp_all [boundPass, executionSites]

theorem sync_preserves_sites (code : Code) :
    executionSites (syncPass code) = executionSites code := by
  induction code <;> simp_all [syncPass, executionSites]

theorem reduction_preserves_sites (code : Code) (inside : Bool) :
    executionSites (reductionPass inside code) = executionSites code := by
  induction code generalizing inside <;> simp_all [reductionPass, executionSites]
  case reduceBatch r => cases inside <;> rfl

theorem pipeline_preserves_sites (code : Code) :
    executionSites (normalize code) = executionSites code := by
  simp [normalize, reduction_preserves_sites, sync_preserves_sites,
    bound_preserves_sites, entry_preserves_sites]

#print axioms pipeline_sound
#print axioms accepted_normal_form

end Clockwork.Core
