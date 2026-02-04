/-
Copyright (c) 2026 TEL Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TEL Team
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Quotient

/-!
# Chain Complexes for Computational Structures

This file defines chain complexes specialized for discrete computational structures
like control flow graphs, programs, and automata.

## Main Definitions

* `ChainComplex` - A sequence of abelian groups with boundary maps satisfying ∂² = 0
* `cycles` - Kernel of boundary map (closed chains)
* `boundaries` - Image of boundary map (exact chains)
* `homology` - Quotient H_n = cycles/boundaries

## Main Results

* `boundaries_in_cycles` - boundaries ⊆ cycles (follows from ∂² = 0)
* `homology_well_defined` - Homology groups are well-defined

## Notation

* `C.module n` - The n-th module in the chain complex
* `∂ n` - The n-th boundary map (C_n → C_{n-1})
* `H_n C` - The n-th homology group

## Implementation Notes

We use ℤ-modules (free abelian groups) to align with computational structures where
elements have integer coefficients (e.g., formal sums of basic blocks).

## References

* [HODGE_IR_DESIGN.md] - Type system with Hodge bidegree
* [algorithmic_khovanov.py] - Python implementation of chain complexes
* [Chapter_03_The_Hodge_Intermediate_Representation.md] - HIR chapter

## Tags

chain complex, homology, boundary operator, ∂²=0, algebraic topology, computation
-/

namespace CondensedTEL

/-! ## Basic Definitions -/

/--
A chain complex is a sequence of ℤ-modules {C_n}_{n≥0} with boundary maps ∂_n : C_n → C_{n-1}
satisfying the fundamental property ∂² = 0.

This structure is specialized for computational analysis:
- C_0 typically represents basic blocks or states
- C_1 typically represents edges or transitions
- C_2 typically represents faces or cycles
-/
structure ChainComplex where
  /-- The module at each degree n (typically Fin k → ℤ for finite-dimensional case) -/
  module : ℕ → Type

  /-- Each module has an abelian group structure -/
  [add_comm_group : ∀ n, AddCommGroup (module n)]

  /-- Boundary map: ∂_n : C_n → C_{n-1}

      For CFGs: ∂_1(edge) = target_vertex - source_vertex
      For programs: ∂ maps control flow to vertex difference -/
  boundary : ∀ n, module n →+ module (n - 1)

  /-- The chain complex axiom: ∂ ∘ ∂ = 0

      Intuitively: "the boundary of a boundary is empty"
      Computationally: paths telescope to zero

      Examples:
      - CFG: summing vertex differences around a cycle gives 0
      - Programs: double differentiation vanishes
      - Type theory: substitution associativity (∂∂ = 0) -/
  boundary_squared_zero : ∀ (n : ℕ) (x : module (n + 1)),
    boundary n (boundary (n + 1) x) = 0

-- Enable dot notation for accessing fields
attribute [instance] ChainComplex.add_comm_group

/-! ## Cycles and Boundaries -/

/--
Cycles at degree n: kernel of ∂_n

These are chains with no boundary (closed chains).
For CFGs: closed paths (start = end)
For programs: loops with balanced control flow
-/
def cycles (C : ChainComplex) (n : ℕ) : AddSubgroup (C.module n) :=
  AddMonoidHom.ker (C.boundary n)

/--
Boundaries at degree n: image of ∂_{n+1}

These are chains that are boundaries of higher-dimensional chains (exact chains).
For CFGs: paths from entry to exit
For programs: straight-line code without loops
-/
def boundaries (C : ChainComplex) (n : ℕ) : AddSubgroup (C.module n) :=
  AddMonoidHom.range (C.boundary (n + 1))

/-! ## Key Theorem: Boundaries are Cycles -/

/--
Every boundary is a cycle: Im(∂_{n+1}) ⊆ Ker(∂_n)

This is the fundamental consequence of ∂² = 0.

Proof: If x = ∂y, then ∂x = ∂∂y = 0, so x ∈ Ker(∂).
-/
theorem boundaries_in_cycles (C : ChainComplex) (n : ℕ) :
    boundaries C n ≤ cycles C n := by
  intro x hx
  -- x is a boundary, so x = ∂y for some y
  obtain ⟨y, rfl⟩ := hx
  -- Need to show ∂x = 0
  simp only [AddSubgroup.mem_mk, AddMonoidHom.mem_ker, cycles]
  -- ∂x = ∂∂y = 0 by chain complex axiom
  exact C.boundary_squared_zero n y

/-! ## Homology -/

/--
The n-th homology group: H_n = Ker(∂_n) / Im(∂_{n+1})

Homology measures "holes" in the complex:
- H_0 = connected components
- H_1 = independent loops (cyclomatic complexity for CFG)
- H_2 = 2-dimensional holes (voids)

Computationally: H_1(CFG) gives the number of independent loops,
which is preserved by optimizations (Hodge-theoretic stability).
-/
def homology (C : ChainComplex) (n : ℕ) : Type :=
  (cycles C n) ⧸ (AddSubgroup.comap (AddSubgroup.subtype (cycles C n)) (boundaries C n))

/-! ## Homology is well-defined -/

/--
Homology groups are well-defined quotients because boundaries ⊆ cycles.

This follows from `boundaries_in_cycles`.
-/
theorem homology_well_defined (C : ChainComplex) (n : ℕ) :
    AddGroup (homology C n) := by
  unfold homology
  infer_instance

/-! ## Examples -/

/--
The trivial chain complex: all modules are {0}.

This has trivial homology everywhere.
-/
def trivial : ChainComplex where
  module := fun _ => Unit
  add_comm_group := fun _ => inferInstanceAs (AddCommGroup Unit)
  boundary := fun _ => {
    toFun := fun _ => ()
    map_zero' := rfl
    map_add' := fun _ _ => rfl
  }
  boundary_squared_zero := fun _ _ => rfl

/-! ## Notation -/

-- Notation for boundary map (uncomment if desired)
-- notation "∂[" C "," n "]" => ChainComplex.boundary C n

/-! ## Remarks on Computational Interpretation -/

/-
**Connection to TEL and Hodge Theory:**

1. **CFG as Chain Complex**: Control flow graphs naturally form chain complexes where:
   - C_0 = basic blocks (vertices)
   - C_1 = edges (control flow)
   - ∂_1(edge) = target - source

2. **Homology = Loops**: H_1(CFG) counts independent loops, equal to cyclomatic complexity.
   This is preserved by compilation/optimization (functoriality).

3. **Hodge Decomposition**: On metric chain complexes, we can decompose C_n as:
   C_n = Exact ⊕ Coexact ⊕ Harmonic
   where Harmonic ≃ H_n (the stable invariant).

4. **Spectral Semantics**: The eigenvalues of the transfer operator (Laplacian) give
   spectral invariants that detect loops and cycles. This is the computational analogue
   of Fourier analysis in Schwartz space.

5. **TEL Axioms from Hodge**:
   - Functoriality: CFG morphisms preserve Hodge structure
   - Completeness: Harmonic forms determined by cycles
   - Computational Content: Hodge decomposition is algorithmic

See `CFGChainComplex.lean` and `HodgeDecomposition.lean` for details.
-/

end CondensedTEL
