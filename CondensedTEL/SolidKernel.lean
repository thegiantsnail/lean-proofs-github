/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.

## Solid Kernel

The solid part of UI state consists of deterministic, projective objects.

### Definition

A sheaf S is **solid** if:
1. S is projective in the category of sheaves
2. Equivalently: S is represented by an extremally disconnected space
3. Concrete meaning: Solid state is deterministic and has no animation

### Examples

- Database state (key-value store)
- Authentication tokens
- Form data (text content)
- Configuration settings
- Scroll position (as discrete value, not animation)
-/

import CondensedTEL.UIPresheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact

universe u v

namespace CondensedTEL

/-! ### Solid Objects -/

/-- A sheaf is solid if it is projective.
Equivalently: extremally disconnected space of realizations.
-/
structure Solid where
  /-- The underlying sheaf -/
  sheaf : Sheaf
  /-- Projectivity: lifts exist against epimorphisms -/
  is_projective : ∀ (A B : Sheaf) (epi : A.presheaf → B.presheaf),
    -- TODO: formalize epi condition
    -- For every map S → B, there exists lift S → A
    True  -- Placeholder

namespace Solid

/-- Example: Constant sheaf is solid (trivially projective) -/
def const (S : Type u) : Solid where
  sheaf := Sheaf.const S
  is_projective := by intro A B epi; trivial

/-- Database state sheaf (stores key-value pairs, deterministic) -/
def database : Solid where
  sheaf := { presheaf := UIPresheaf.const (String → Option String)
             is_sheaf := by sorry }
  is_projective := by intro A B epi; trivial

end Solid

/-! ### Liquid Objects -/

/-- A sheaf is liquid if it's the "non-deterministic completion" of state.

Liquid objects include:
- Animation state (time-dependent interpolation)
- Async loading indicators
- Scroll inertia (physics simulation)
- Network latency compensation
-/
structure Liquid where
  /-- The underlying sheaf -/
  sheaf : Sheaf
  /-- Has non-trivial Ext¹ with some solid object -/
  has_nontrivial_ext : ∃ (S : Solid), True  -- Ext¹(L, S) ≠ 0 placeholder

namespace Liquid

/-- Animation state (interpolates between keyframes, non-deterministic) -/
def animation : Liquid where
  sheaf := { presheaf := UIPresheaf.const (ℕ → ℝ)  -- frame → position
             is_sheaf := by sorry }
  has_nontrivial_ext := by exists Solid.const Unit; trivial

end Liquid

/-! ### Short Exact Sequence Decomposition -/

/-- Every UI state sheaf fits into a short exact sequence:

    0 → S → UI → L → 0

where S is solid (deterministic core) and L is liquid (effects).
-/
structure SESDecomposition (UI : Sheaf) where
  /-- Solid part -/
  solid : Solid
  /-- Liquid part -/
  liquid : Liquid
  /-- Inclusion S ↪ UI -/
  inclusion : solid.sheaf.presheaf → UI.presheaf
  /-- Projection UI ↠ L -/
  projection : UI.presheaf → liquid.sheaf.presheaf
  /-- Exactness at UI -/
  exact : True  -- TODO: formalize Im(inclusion) = Ker(projection)
  /-- Monomorphism condition -/
  mono : True  -- TODO: inclusion is injective
  /-- Epimorphism condition -/
  epi : True  -- TODO: projection is surjective

/-! ### Splitting Criterion -/

/-- The SES splits iff Ext¹(L, S) = 0 (no patch entanglement).

When it splits: UI ≅ S ⊕ L (direct sum, no interaction)
When it doesn't split: S and L are entangled (race conditions, etc.)
-/
def SESDecomposition.splits {UI : Sheaf} (ses : SESDecomposition UI) : Prop :=
  -- Splitting means there exists a section L → UI such that projection ∘ section = id
  ∃ (section : ses.liquid.sheaf.presheaf → UI.presheaf),
    True  -- TODO: formalize projection ∘ section = id_L

/-- Main theorem: SES splits ↔ Ext¹(L, S) = 0 -/
theorem ses_splits_iff_ext_vanishes {UI : Sheaf} (ses : SESDecomposition UI) :
    ses.splits ↔ True := by  -- TODO: Ext¹(ses.liquid, ses.solid) = 0
  sorry

/-! ### Concrete Examples -/

/-- Example: Simple counter with animation -/
def counterWithAnimation : SESDecomposition (Sheaf.const UIState) where
  solid := Solid.const ℕ  -- Counter value (solid)
  liquid := Liquid.animation  -- Increment animation (liquid)
  inclusion := by sorry
  projection := by sorry
  exact := by trivial
  mono := by trivial
  epi := by trivial

-- Counter animation splits (no entanglement)
example : counterWithAnimation.splits := by
  unfold SESDecomposition.splits
  exists (fun _ => sorry)
  trivial

end CondensedTEL
