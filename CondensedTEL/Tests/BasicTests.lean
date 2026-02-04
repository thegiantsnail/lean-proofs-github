/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.

## Basic Validation Tests

Simple tests to validate the core definitions compile and make sense.
-/

import CondensedTEL.FrameWindow
import CondensedTEL.UIPresheaf
import CondensedTEL.FrameDeterministic

namespace CondensedTEL.Tests

open CondensedTEL

/-! ### Basic Frame Window Tests -/

/-- Example: Simple frame window with two clicks -/
def exampleFrame1 : FrameWindow := {
  interval := { start := 0, finish := 100, valid := by norm_num }
  frameRate := 60
  events := [
    UIEvent.mouseClick 10 20 50,
    UIEvent.mouseClick 30 40 75
  ]
  events_in_interval := by
    intro e he
    simp [List.mem_cons, List.mem_singleton] at he
    cases he with
    | inl h => subst h; constructor <;> norm_num
    | inr h =>
      cases h with
      | inl h => subst h; constructor <;> norm_num
      | inr h => cases h
}

/-- Example: Subframe of exampleFrame1 -/
def exampleSubframe : FrameWindow :=
  exampleFrame1.restrict 
    { start := 40, finish := 80, valid := by norm_num }
    (by unfold LE.le instLEFrameWindow; constructor <;> norm_num)

-- Test that subframe relation is reflexive
example : exampleFrame1 ≤ exampleFrame1 := PartialOrder.le_refl _

/-! ### Presheaf Tests -/

/-- Test constant presheaf -/
def testConstPresheaf : UIPresheaf := UIPresheaf.const ℕ

-- Verify functoriality for constant presheaf
example (F G : FrameWindow) (h : F ≤ G) (n : ℕ) :
    testConstPresheaf.map h n = n :=
  rfl

/-! ### Frame Determinism Tests -/

/-- Trivial replay function (ignores events) -/
def trivialReplay : ReplayFunction where
  replay := fun _ => {
    representation := "constant"
    appState := "0"
    renderData := none
  }
  sorted_equiv := by intros; rfl

-- Trivial replay is frame-deterministic (every cover gives same state)
example : FrameDeterministic trivialReplay := by
  intro W cover
  exists trivialReplay.replay (EventSequence.fromFrame W)
  intro i
  rfl

/-! ### Coverage Tests -/

/-- Identity cover is valid -/
example (F : FrameWindow) : CoverFamily F :=
  CoverFamily.id F

#check exampleFrame1
#check exampleSubframe
#check testConstPresheaf
#check trivialReplay

end CondensedTEL.Tests
