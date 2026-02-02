import Lake
open Lake DSL

package «universal_equivalence» where
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

@[default_target]
lean_lib UniversalEquivalence where
  -- All theorem files in root directory
  srcDir := "."
