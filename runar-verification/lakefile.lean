import Lake
open Lake DSL

package «runar-verification» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib RunarVerification where
  roots := #[`RunarVerification]

lean_exe goldenLoad where
  root := `tests.GoldenLoad
  supportInterpreter := true

lean_exe roundtrip where
  root := `tests.Roundtrip
  supportInterpreter := true

lean_exe pipelineGolden where
  root := `tests.PipelineGolden
  supportInterpreter := true

lean_exe differential where
  root := `tests.Differential
  supportInterpreter := true

lean_exe pipelineConformance where
  root := `tests.PipelineConformance
  supportInterpreter := true

lean_exe typecheckSweep where
  root := `tests.TypeCheckSweep
  supportInterpreter := true

lean_exe omnibusInstantiation where
  root := `tests.OmnibusInstantiation
  supportInterpreter := true
