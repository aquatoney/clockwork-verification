import Lake
open Lake DSL

package clockworkVerification

@[default_target]
lean_lib ClockworkProof where
  roots := #[`Clockwork, `Core, `DSL, `Semantics, `Trace, `Bridge, `Execution,
    `ExecutionTrace, `ExecutionObligations, `Examples, `DES, `DESExamples]
