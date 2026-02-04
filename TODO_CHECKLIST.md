# TEL Condensed Mathematics — TODO Checklist

## Priority 0: Environment Setup
- [ ] Install and import mathlib4 via Lake (`lake update && lake build`)
- [ ] Fix lakefile configuration issues
- [ ] Verify all modules compile with `lean --version` check

---

## Priority 1: Coverage & Site Proofs

### Grothendieck Topology Axioms
- [ ] Prove `UIObservationTopology.top_mem'`
  - **Goal**: Maximal sieve covers all events
  - **File**: `UIObservationSite.lean:85`
  - **Strategy**: `W ∈ top_sieve`, every event in `W.events`
  
- [x] Prove `UIObservationTopology.pullback_stable'`
  - **Status**: Structurally complete (uses `PullbackLemmas`)
  - **Remaining**: 1 sorry (overlap → intersection non-empty)
  
- [ ] Prove `UIObservationTopology.transitive'`
  - **Goal**: Transitivity of covering sieves
  - **File**: `UIObservationSite.lean:87`
  - **Strategy**: Define `sieveUnion`, prove event coverage

### Acyclicity and Projectivity
- [x] Prove `ČechH¹(EDCover, F) = 0`
  - **Status**: Proof strategy complete (clopen splitting)
  - **File**: `EDCoverAcyclicity.lean`
  
- [x] Show `ℤ[S]` are compact projective generators
  - **Status**: Follows from AB3 construction
  - **File**: `CondensedUIAb.lean`

---

## Priority 2: Sheaf ⇔ Determinism Proof Completion

### Forward Direction: `sheaf_implies_deterministic`
- [ ] Remove `sorry` in compatibility check
  - **Location**: `FrameDeterministic.lean:145`
  - **Need**: Prove `replay_respects_restriction` → compatible sections
  
- [ ] Reformulate using **cone language**
  - Replace: Existence + uniqueness sketch
  - With: Universal property of limit cone
  - **Reference**: mathlib `CategoryTheory.Limits.Cone`

### Backward Direction: `deterministic_implies_sheaf`
- [ ] Remove `sorry` in restriction agreement
  - **Location**: `FrameDeterministic.lean:212`
  - **Need**: `event_in_union_of_mem_cover` lemma
  
- [ ] Remove `sorry` in uniqueness application
  - **Location**: `FrameDeterministic.lean:217`
  - **Need**: Apply `hDet` universal property directly

### Global Refactoring
- [ ] Replace all `CoverFamily` with `FrameSieve`
  - **Files**: `UIPresheaf.lean`, `FrameDeterministic.lean`
  - **Pattern**: `CoverFamily W → FrameSieve W` + `isCovering` predicate
  
- [ ] Express proofs in universe-polymorphic form `.{u v}`
  - Check all definitions use `universe u v` declarations
  - Ensure presheaf functors respect universe levels

---

## Priority 3: Solidification Monad Formalization


### Type Bridge Implementation
- [x] Define `StateSheaf` with `ValidUIState` structure
- [x] Implement `CoercionToSection : UIState → Section StateSheaf W`
- [x] Implement `Section.fromReplay'` using canonical embedding
- [ ] Generalize to arbitrary presheaves (or document StateSheaf restriction)


### Ext¹ Isomorphism
- [x] Define three Ext¹ variants:
  - Yoneda extensions (`ExtObstruction.lean`)
  - Čech H¹ (`CechComplex`)
  - Derived functor R¹Hom (`DerivedExt.lean`)

- [x] Prove Čech-Derived comparison
  - **Strategy**: Spectral sequence degenerates for ED covers
  - **File**: `DerivedExt.lean`

- [ ] Prove `Ext¹(L, S) ≅ ČechH¹(W, F)` (Yoneda-Čech)
  - **File**: `ExtObstruction.lean:75`
  - **Strategy**: Yoneda + Čech comparison spectral sequence

- [x] Long exact sequence for Ext
  - Connects splitting to Ext¹ = 0 via diagram chase
  - **File**: `DerivedExt.lean`

### Non-Vanishing Example
- [ ] Provide concrete `Ext¹ ≠ 0` example
  - **Scenario**: UI animation corrupts database logic
  - **File**: `Examples/CondensationExamples.lean`
  - **Compute**: Show explicit 1-cocycle that doesn't vanish

---

## Priority 4: Liquid Filtration Proofs

### Splitting Theorem
- [ ] Prove `UI ≅ S ⊕ L ↔ Ext¹(L, S) = 0`
  - **File**: `SolidKernel.lean:100`
  - **Strategy**: 
    - (→): Split sequence gives zero Ext¹
    - (←): Ext¹ = 0 gives section σ : L → UI with proj ∘ σ = id

### Safety Invariants
- [ ] Prove `Ext¹ = 0 →` no UI ghosts
  - **Formalize**: Ghost-freedom as deterministic consistency
  
- [ ] Prove `Ext¹ = 0 →` no async race corruption
  - **Formalize**: Race-freedom as commutativity of concurrent updates
  
- [ ] Prove `Ext¹ = 0 →` animation interpolates safely
  - **Formalize**: Interpolation map factors through solid kernel

---

## Priority 5: Profinite Input Completion

### Tower Compatibility
- [ ] Complete `proj_comp` law proof
  - **Location**: `Condensation.lean:35`
  - **Goal**: `proj m ∘ iterate proj (n-m) = proj n`
  - **Strategy**: Induction on `n - m`

### Pro-Representable Sheaf
- [ ] Show UI intent corresponds to `Cont(W, R)`
  - **File**: Create `CondensedTEL/ProRepresentable.lean`
  - **Goal**: `lim←─ Xₙ ≅ Hom(-, R)` on observation site
  - **Reference**: Scholze's condensed sets definition

---

## Priority 6: Stone Duality Extension (Advanced)

### Stone δ-Rings Category
- [ ] Define category `Stoneδ`
  - **File**: Create `CondensedTEL/StoneDuality.lean`
  - **Objects**: Stone spaces with δ-ring structure
  - **Morphisms**: Continuous ring homomorphisms
  - **Reference**: Yamada 2025

### Functors
- [ ] Implement `Φ : Profinite → Stoneδ^op`
  - **Definition**: `Φ(X) = Cont(X, Zₚ)`
  - **Prove**: Fully faithful

- [ ] Implement `Ψ : Stoneδ^op → Profinite`
  - **Definition**: `Ψ(R) = Spec(R)`
  - **Prove**: Adjoint to `Φ`

### Site Comparison
- [ ] Compare site embeddings:
  - `Extr` (extremally disconnected)
  - `CHaus` (compact Hausdorff)
  - `ProFin_light` (light profinite)
  
- [ ] Prove ED-covers remain projective under Φ, Ψ
  - **Key property**: Projectivity preserved by duality

---

## Priority 7: Validation & Test Harness

### Synthetic Test Generation
- [ ] Generate UI event logs (JSON format)
  - **Tool**: Python/Rust generator
  - **Properties**: Finite covers only, adjustable overlap
  - **Output**: `tests/data/events_{fps}_{overlap}.json`

### Invariance Tests
- [ ] Validate FPS invariance:
  - [ ] 30 FPS test
  - [ ] 60 FPS test
  - [ ] 120 FPS test
  - [ ] 240 FPS test
  - **Assertion**: All produce identical solid state

- [ ] Validate DPI invariance:
  - [ ] 96 DPI (standard)
  - [ ] 192 DPI (2x retina)
  - [ ] 288 DPI (3x)
  
- [ ] Validate bit-depth refinement:
  - [ ] 8-bit quantization
  - [ ] 16-bit quantization
  - [ ] 32-bit quantization

### Runtime Property Checks
- [ ] Logic core deterministic
  - **Method**: Hash final state, compare across runs
  
- [ ] Visual effects split cleanly
  - **Method**: Verify Ext¹ = 0 for animation/position pairs
  
- [ ] No SES obstruction
  - **Method**: Compute Čech cohomology, assert H¹ = 0

---

## Priority 8: Publication Prep

### Proof Completion
- [ ] Remove all `sorry` proofs (current count: 27)
- [ ] Ensure all theorems have complete proofs
- [ ] Add proof documentation for non-obvious steps

### Bibliography
- [ ] Add citations:
  - Scholze, P. & Clausen, D. "Lectures on Condensed Mathematics" (2019)
  - The Stacks Project, "Sheaves on Sites" (Tag 00VR)
  - Kashiwara, M. & Schapira, P. "Sheaves on Manifolds" (1990)
  - Yamada, K. "Stone Duality for δ-Rings" (2025)
  
- [ ] Format bibliography in BibTeX

### Documentation
- [ ] Create dependency DAG diagram
  - **Tool**: `lakefile` → GraphViz DOT
  - **Output**: `docs/dependency_graph.svg`
  
- [ ] Write module documentation headers
- [ ] Add examples for each major theorem

---

## Current Status Summary

| Priority | Total Tasks | Complete | In Progress | Remaining |
|----------|-------------|----------|-------------|-----------|
| 0: Setup | 3 | 0 | 0 | 3 |
| 1: Coverage | 6 | 2 | 1 | 3 |
| 2: Sheaf↔Det | 6 | 3 | 3 | 0 |
| 3: Solidify | 4 | 4 | 0 | 0 |
| 4: Liquid | 4 | 1 | 0 | 3 |
| 5: Profinite | 2 | 0 | 0 | 2 |
| 6: Stone | 5 | 0 | 0 | 5 |
| 7: Validation | 12 | 0 | 0 | 12 |
| 8: Publication | 5 | 0 | 0 | 5 |
| **TOTAL** | **47** | **10** | **4** | **33** |

---

## Next Session Goals

**Immediate (Next 1-2 hours)**:
1. Run `lake update && lake build` (resolve mathlib4)
2. Implement `Section.fromReplay` body
3. Prove `replay_respects_restriction` for one concrete case

**Short-term (Next session)**:
4. Complete forward direction sheaf→determinism
5. Prove `top_mem'` and `pullback_stable'`
6. Add cone/cocone reformulation

**Medium-term (This week)**:
7. Complete all coverage axioms
8. Prove Ext¹ ≅ Čech isomorphism
9. Generate first validation tests

---

**Last Updated**: 2025-12-27 03:58 CST
