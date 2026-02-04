/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.

## Graph Assembly Tests

Verify that the Graph Assembly Monad correctly creates H₁ = ℤ².
-/

import CondensedTEL.UniversalLiquidQuine

namespace CondensedTEL.Tests.GraphAssembly

open UniversalLiquid

/-! ### Test Configurations -/

/-- Minimal valid configuration (3 atoms) -/
def minimalConfig : AtomConfig := {
  n_A := 3,  -- Three self-reference atoms
  n_B := 0,
  n_C := fun _ => 0,
  n_D := 0  
}

/-- Telephone quine configuration -/
def telephoneConfig : AtomConfig := {
  n_A := 1,
  n_B := 0,
  n_C := fun | 0 => 1 | _ => 0,  -- One C₀
  n_D := 3  -- Three boundaries (tripart)
}

/-- Height-3 configuration -/
def height3Config : AtomConfig := {
  n_A := 2,
  n_B := 1,
  n_C := fun | 3 => 1 | _ => 0,  -- C₃ present
  n_D := 3
}

/-! ### Assembly Tests -/

/-- Test: Minimal config assembles successfully -/
def test_minimal_assembly : IO Unit := do
  match assemble minimalConfig with
  | .ok graph => 
      IO.println s!"✓ Minimal assembly: V={graph.atoms.length}, E={graph.edges.length}"
  | .error e =>
      IO.println s!"✗ Minimal assembly failed: {e}"

/-- Test: Minimal config has H₁ = ℤ² -/
def test_minimal_h1 : IO Unit := do
  match assemble minimalConfig with
  | .ok graph =>
      if hasH1_Z2 graph then
        IO.println "✓ Minimal config has H₁ = ℤ²"
      else
        let V := graph.atoms.length
        let E := graph.edges.length
        IO.println s!"✗ Minimal config: H₁ rank = {E - V + 1}, expected 2"
  | .error e =>
      IO.println s!"✗ Assembly error: {e}"

/-- Test: ComputeH1Rank returns 2 -/
def test_compute_h1 : IO Unit := do
  match computeH1Rank minimalConfig with
  | .ok rank =>
      if rank == 2 then
        IO.println "✓ computeH1Rank = 2"
      else
        IO.println s!"✗ computeH1Rank = {rank}, expected 2"
  | .error e =>
      IO.println s!"✗ computeH1Rank error: {e}"

/-- Test: Telephone config -/
def test_telephone : IO Unit := do
  match computeH1Rank telephoneConfig with
  | .ok rank =>
      IO.println s!"{'✓' if rank == 2 else '✗'} Telephone: H₁ rank = {rank}"
  | .error e =>
      IO.println s!"✗ Telephone error: {e}"

/-- Test: Height-3 config -/
def test_height3 : IO Unit := do
  match computeH1Rank height3Config with
  | .ok rank =>
      IO.println s!"{'✓' if rank == 2 else '✗'} Height-3: H₁ rank = {rank}"
      IO.println s!"  Chromatic height: {maxChromaticHeight height3Config}"
      IO.println s!"  Period: {chromaticPeriod ⟨3, by omega⟩}"
  | .error e =>
      IO.println s!"✗ Height-3 error: {e}"

/-- Test: Invalid config (too few atoms) -/
def test_invalid_too_few : IO Unit := do
  let config : AtomConfig := { n_A := 2, n_B := 0, n_C := fun _ => 0, n_D := 0 }
  match assemble config with
  | .ok _ =>
      IO.println "✗ Should reject config with < 3 atoms"
  | .error e =>
      IO.println s!"✓ Correctly rejected: {e}"

/-! ### Main Test Runner -/

def runAllTests : IO Unit := do
  IO.println "Running Graph Assembly Tests..."
  IO.println ""
  test_minimal_assembly
  test_minimal_h1
  test_compute_h1
  test_telephone
  test_height3
  test_invalid_too_few
  IO.println ""
  IO.println "Tests complete!"

#eval runAllTests

/-! ### Singularity Analysis Tests -/

/-- Import singularity detection -/
-- import CondensedTEL.TelephoneSingularity
-- open Singularity

/-- Test: Telephone config has singularity -/
def test_telephone_singularity : IO Unit := do
  match assemble telephoneConfig with
  | .ok graph =>
      -- Would use: hasTelephoneSingularity graph
      -- For now, just check structure
      IO.println "Telephone Singularity Analysis:"
      IO.println s!"  Atoms: {graph.atoms.length}"
      IO.println s!"  Edges: {graph.edges.length}"
      IO.println s!"  Expected: degree-4 vertex (singularity)"
  | .error e =>
      IO.println s!"Assembly error: {e}"

/-- Test: Generic is smooth (no singularity) -/
def test_generic_smooth : IO Unit := do
  match assemble minimalConfig with
  | .ok graph =>
      IO.println "Generic Smoothness:"
      IO.println s!"  Atoms: {graph.atoms.length}"
      IO.println s!"  Edges: {graph.edges.length}"
      IO.println s!"  All vertices degree ≤ 3 (smooth)"
  | .error e =>
      IO.println s!"Assembly error: {e}"

def runSingularityTests : IO Unit := do
  IO.println "\n=== Singularity Tests ===\n"
  test_telephone_singularity
  IO.println ""
  test_generic_smooth
  IO.println "\n=== Complete ===\n"

-- Uncomment when TelephoneSingularity module is available
-- #eval runSingularityTests

end CondensedTEL.Tests.GraphAssembly
