import Lake
open Lake DSL

package clockworkVerification

@[default_target]
lean_lib ClockworkProof where
  roots := #[`Clockwork, `Core, `DSL, `Semantics, `Trace]
