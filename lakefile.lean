import Lake
open Lake DSL

package «universal_equivalence» where
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

@[default_target]
lean_lib «universal_equivalence» where
  -- Theorem files are in root and CondensedTEL/Examples
  roots := #[`UniversalEquivalencePattern, `Theorem1_FrameDeterministic,
             `Theorem2_ThinTreeDeterminism, `Theorem3_LanglandsTheorem,
             `Theorem4_ProgramSemantics]
  globs := #[.submodules `CondensedTEL]
