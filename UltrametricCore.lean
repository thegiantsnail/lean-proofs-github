/-!
Core definitions for ultrametric-based structures and structure-preserving maps.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic

universe u v

/-- Shared ultrametric structure: a distance with strong triangle inequality. -/
class UltrametricStructure (α : Type u) where
  d : α → α → ℝ
  ultra : ∀ x y z, d x z ≤ max (d x y) (d y z)

namespace UltrametricStructure

variable {α : Type u} [U : UltrametricStructure α]

/-- Ultrametric ball: elements at distance ≤ r from x. -/
def Ball (x : α) (r : ℝ) : Set α :=
  {y | U.d x y ≤ r}

/-- Ultrametric covering: collection of balls covering a set. -/
structure Cover (S : Set α) where
  radii : ℕ → ℝ
  centers : ℕ → α
  covers : S ⊆ ⋃ n, Ball (centers n) (radii n)

end UltrametricStructure

/-- Structure-preserving equivalence between propositions. -/
structure PropEquiv (P Q : Prop) : Prop where
  to : P → Q
  inv : Q → P

/-- Isometry between ultrametric structures. -/
structure UltrametricIsometry {α : Type u} {β : Type v}
    (U : UltrametricStructure α) (V : UltrametricStructure β) where
  map : α → β
  preserves : ∀ x y, V.d (map x) (map y) = U.d x y

/-- Order-preserving embedding between preorders. -/
structure OrderPreservingEmbedding {α : Type u} {β : Type v}
    [Preorder α] [Preorder β] where
  map : α → β
  monotone : ∀ {x y}, x ≤ y → map x ≤ map y
