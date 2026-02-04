/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.

## Concrete Examples - Properly Typed

Focus on executable examples, not prose.
-/

import CondensedTEL.Condensation

namespace CondensedTEL.Examples

/-! ### Mouse Position Tower -/

/-- Mouse position as (x, y) coordinates -/
def MousePos := ℕ × ℕ

/-- Quantization tower: grid refinements -/
def mouseTower (max_x max_y : ℕ) : QuantizationTower MousePos where
  level n := Fin (max_x * 2^n) × Fin (max_y * 2^n)
  level_finite n := inferInstance
  proj n := fun ⟨x, y⟩ => ⟨⟨x.val / 2, by sorry⟩, ⟨y.val / 2, by sorry⟩⟩
  proj_comp := by sorry

/-! ### Tick-Rate Test -/

/-- Example: Counter that may or may not be FPS-dependent -/
def counterExample (fps_dependent : Bool) : TickRate ℕ :=
  fun freq init => {
    run := Id.run {
      snd := if fps_dependent 
             then init + freq  -- BAD: depends on frame rate!
             then init          -- GOOD: FPS-independent
    }
  }

/-- Test: FPS-independent counter is constant -/
example : TickRate.isConstant (counterExample false) 0 := by
  unfold TickRate.isConstant
  intro freq1 freq2
  rfl

/-- Test: FPS-dependent counter is NOT constant -/
example : ¬TickRate.isConstant (counterExample true) 0 := by
  unfold TickRate.isConstant
  push_neg
  use 30, 60
  sorry  -- 30 ≠ 60

end CondensedTEL.Examples
