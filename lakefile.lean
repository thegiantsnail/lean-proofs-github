import Lake
open Lake DSL

package «condensed_tel» where
  -- Prefer release builds for mathlib to speed up compilation
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

-- ⭐ LeanArchitect dependency for blueprint generation
-- TODO: Temporarily disabled due to LeanArchitect lakefile build issue
-- require Architect from git
--   "https://github.com/hanwenzhu/LeanArchitect"

@[default_target]
lean_lib CondensedTEL where
  -- Add source directories
  globs := #[.submodules `CondensedTEL]

lean_exe nullsth where
  root := `CondensedTEL.NullSTHOperational
  supportInterpreter := true

lean_exe contracts where
  root := `CondensedTEL.OperatorContractsCLI
  supportInterpreter := true

lean_exe composed_contracts where
  root := `CondensedTEL.ComposedContractsCLI
  supportInterpreter := true
