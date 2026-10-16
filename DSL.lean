import Core

namespace Clockwork.Core

-- The executable conservative core. A batch contains dependency-ordered
-- parallel groups; per-domain effects have already been resolved by Binding.
inductive Stage where
  | sequential (window : Nat) (handlers : List Access)
  | batch (window : Nat) (groups : List (List Access)) (accumulators : List Nat)
  | partition (plan : Plan) (crossEffects : List Access) (child : Stage)
  | filter (fn : Transform) (child : Stage)
  | choice (guard : Nat) (yes no : Stage)
  | repeat (body : Stage)
  | repartition (plan : Plan) (child : Stage)
  | terminate

structure Program where
  horizon : Nat
  body : Stage

def batchReductions : List Nat -> Code
  | [] => .stop
  | r :: rest => .seq (.reduceBatch r) (batchReductions rest)

def batchGroups (accumulators : List Nat) : List (List Access) -> Code
  | [] => .stop
  | group :: rest =>
      .seq (.execute true group) (.seq (batchReductions accumulators) (batchGroups accumulators rest))

def admitWindow (stream : Bool) (window : Nat) (work : Code) : Code :=
  if stream then work else .seq (.drain (.literal window)) work

def lower (stream : Bool) : Stage -> Code
  | .sequential w handlers => admitWindow stream w (.execute false handlers)
  | .batch w groups accumulators => admitWindow stream w (batchGroups accumulators groups)
  | .partition p e child =>
      .domain p e .effective (lower true child) (.routeAnnounce .effective) []
  | .filter f child =>
      if stream then .seq (.transform f) (lower true child) else .invalid
  | .choice guard yes no => .branch guard (lower stream yes) (lower stream no)
  | .repeat body => .loop (lower stream body)
  | .repartition p child => .seq (.reassign p) (lower stream child)
  | .terminate => .stop

theorem batchReductions_bounded (accumulators : List Nat) (inside : Bool) :
    Bounded inside (batchReductions accumulators) := by
  induction accumulators <;> simp_all [batchReductions, Bounded]

theorem batchGroups_bounded (accumulators : List Nat) (groups : List (List Access))
    (inside : Bool) : Bounded inside (batchGroups accumulators groups) := by
  induction groups <;> simp_all [batchGroups, Bounded, batchReductions_bounded]

-- The current frontend already passes the active admission bound to children.
-- The IR pass additionally establishes this property on uncoordinated core IR.
theorem lowering_respects_admission (stage : Stage) (stream : Bool) :
    Bounded stream (lower stream stage) := by
  induction stage generalizing stream <;>
    cases stream <;> simp_all [lower, admitWindow, Bounded, batchGroups_bounded]

structure Executable where
  horizon : Nat
  code : Code
  deriving DecidableEq

def compileProgram (nodes : List Nat) (program : Program) : Option Executable :=
  (compile nodes (.loop (lower false program.body))).map
    (fun code => {horizon := program.horizon, code := code})

theorem dsl_pipeline_sound (nodes : List Nat) (program : Program) (output : Executable)
    (accepted : compileProgram nodes program = some output) :
    output.horizon = program.horizon /\ Invariants nodes output.code := by
  unfold compileProgram at accepted
  cases result : compile nodes (.loop (lower false program.body)) with
  | none => simp [result] at accepted
  | some code =>
      simp only [result, Option.map_some] at accepted
      have same := Option.some.inj accepted
      subst output
      exact And.intro rfl (pipeline_sound nodes _ code result)

-- A nonempty witness prevents an acceptance theorem from hiding a compiler
-- that rejects every program. The examples also exercise both validators.
def samplePlan : Plan := [[0], [1]]
def lane0 : Access := { reads := [0], writes := [0] }
def lane1 : Access := { handler := 1, reads := [1], writes := [1] }

def partitionBatch : Program :=
  { horizon := 10,
    body := .partition samplePlan [lane0, lane1]
      (.batch 10 [[lane0, lane1]] [7]) }

example : (compileProgram [0, 1] partitionBatch).isSome = true := by decide

def partitionChoiceFilter : Program :=
  { horizon := 10,
    body := .partition samplePlan [lane0, lane1]
      (.choice 0
        (.filter {name := 0, domainPreserving := true} (.sequential 10 [lane0, lane1]))
        (.sequential 10 [lane0, lane1])) }

example : (compileProgram [0, 1] partitionChoiceFilter).isSome = true := by decide

example : compileProgram [0, 1]
    { horizon := 10,
      body := .filter {name := 0, domainPreserving := true} (.sequential 10 [lane0]) }
      = none := by decide

example : (compileProgram [0, 1]
    { horizon := 10,
      body := .repeat (.choice 0
        (.repartition [[1], [0]] (.partition [[1], [0]] [lane0, lane1] (.sequential 10 [lane0, lane1])))
        (.partition samplePlan [lane0, lane1] (.sequential 10 [lane0, lane1]))) }).isSome = true := by decide

example : compileProgram [0, 1]
    { horizon := 10, body := (.partition [[0], [0, 1]] [lane0, lane1]
      (.batch 10 [[lane0, lane1]] [7])) } = none := by decide

example : compileProgram [0, 1]
    { horizon := 10, body := (.partition samplePlan [lane0, lane0]
      (.batch 10 [[lane0, lane0]] [7])) } = none := by decide

def brokenRound : Code :=
  .domain samplePlan [lane0, lane1] (.literal 10)
    (.seq (.drain (.literal 10)) (.reduceBatch 7))
    (.announceRoute (.literal 10)) []

example : Bounded false brokenRound -> False := by simp [Bounded, brokenRound]
example : Ordered brokenRound -> False := by simp [Ordered, brokenRound]
example : Reduced false brokenRound -> False := by simp [Reduced, brokenRound]
example : (compile [0, 1] brokenRound).isSome = true := by decide

def outerFilter (preserves : Bool) : Code :=
  .entry {name := 0, domainPreserving := preserves} samplePlan [lane0, lane1]
    (.literal 10) (.execute true [lane0, lane1]) (.announceRoute (.literal 10)) []

example : (compile [0, 1] (outerFilter true)).isSome = true := by decide
example : compile [0, 1] (outerFilter false) = none := by decide

#print axioms dsl_pipeline_sound

end Clockwork.Core
