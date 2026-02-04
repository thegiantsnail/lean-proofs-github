/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.

## UI State Presheaves

Presheaves of UI state over the frame window site. A presheaf assigns:
- To each frame window F: a set of possible UI states
- To each restriction F → G: a restriction map on states

### Key Concepts

- **Presheaf**: Contravariant functor from frame windows to sets (or types)
- **Restriction map**: How state "restricts" to smaller time windows
- **Gluing condition**: When local states on covers determine global state uniquely
-/

import CondensedTEL.FrameWindow
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Types

universe u v

namespace CondensedTEL

/-! ### UI State Type -/

/-- Abstract UI state type (will be specialized later) -/
structure UIState where
  /-- DOM tree or abstract UI representation -/
  representation : String  -- Simplified; could be tree structure
  /-- Application-specific state -/
  appState : String
  /-- Frame-local rendering data -/
  renderData : Option String

namespace UIState

/-- Trivial restriction (loses no information) -/
def restrict (s : UIState) (F G : FrameWindow) (h : F ≤ G) : UIState :=
  s  -- Identity restriction for now; could filter renderData

/-- Two states are compatible if they agree on their intersection -/
def compatible (s1 s2 : UIState) (F G : FrameWindow) : Prop :=
  -- Simplified compatibility: structural equality
  -- In reality, would check agreement on intersection events
  s1.representation = s2.representation ∧ s1.appState = s2.appState

end UIState

/-! ### Presheaf Structure -/

/-- A presheaf of UI states assigns a type of states to each frame window,
with restriction maps that are functorial.

For now, this is a simplified definition. Full categorical presheaf structure
would use `(FrameWindow.site)ᵒᵖ ⥤ Type*`.
-/
structure UIPresheaf where
  /-- States for each frame window -/
  obj : FrameWindow → Type u
  /-- Restriction maps (contravariant) -/
  map : ∀ {F G : FrameWindow}, (F ≤ G) → obj G → obj F
  /-- Functoriality: restricting to self is identity -/
  map_id : ∀ (F : FrameWindow) (s : obj F),
    map (PartialOrder.le_refl F) s = s
  /-- Functoriality: composition of restrictions -/
  map_comp : ∀ {F G H : FrameWindow} (hFG : F ≤ G) (hGH : G ≤ H) (s : obj H),
    map hFG (map hGH s) = map (PartialOrder.le_trans F G H hFG hGH) s

namespace UIPresheaf

/-- Constant presheaf (same state at all frames) -/
def const (S : Type u) : UIPresheaf where
  obj := fun _ => S
  map := fun _ s => s
  map_id := fun _ _ => rfl
  map_comp := fun _ _ _ => rfl

/-- Presheaf of UI events (varying by frame) -/
def eventPresheaf : UIPresheaf where
  obj := fun F => List UIEvent
  map := fun {F G} hFG events =>
    -- Restrict to events in F's interval
    events.filter (fun e => F.interval.start ≤ e.timestamp ∧ e.timestamp ≤ F.interval.finish)
  map_id := by intro F s; sorry  -- Requires filter theorem
  map_comp := by intro F G H hFG hGH s; sorry

end UIPresheaf

/-! ### Sections and Gluing -/

/-- A section of a presheaf F over a frame window W assigns a value in F(W) -/
def Section (F : UIPresheaf) (W : FrameWindow) : Type u :=
  F.obj W

/-- Restriction of a section to a subframe -/
def Section.restrict {F : UIPresheaf} {W V : FrameWindow} (h : V ≤ W)
    (s : Section F W) : Section F V :=
  F.map h s

/-! ### Critical Type Bridge: Replay → Section -/

/-- Restrict events to a subframe interval -/
def EventSequence.restrictTo (events : List UIEvent) (I : TimeInterval) : List UIEvent :=
  events.filter (fun e => I.start ≤ e.timestamp ∧ e.timestamp ≤ I.finish)

/-- The semantic axiom of TEL replay: replaying restricted events
    equals restricting the replayed state.

This is the fundamental coherence condition connecting computational
replay with sheaf-theoretic restrictions. -/
axiom replay_respects_restriction (replay : ReplayFunction)
    {W V : FrameWindow} (h : V ≤ W) :
    replay.replay (W.events.restrictTo V.interval) =
    (replay.replay W.events).restrict V W h

/-- Lift a UIState to a section of StateSheaf -/
def UIState.toSection (s : UIState) (W : FrameWindow)
    (h : ∃ replay : ReplayFunction, replay.replay W.events = s) :
    Section StateSheaf.presheaf W :=
  {
    state := s
    is_valid := h
  }

/-- Extract UIState from a section of StateSheaf -/
def Section.toUIState {W : FrameWindow} (sec : Section StateSheaf.presheaf W) : UIState :=
  sec.state

/-- For general presheaves with a canonical state projection -/
class HasStateProjection (F : UIPresheaf) where
  /-- Project a section to its underlying UIState -/
  toState : ∀ {W : FrameWindow}, Section F W → UIState
  /-- Projection respects restrictions -/
  toState_restrict : ∀ {W V : FrameWindow} (h : V ≤ W) (s : Section F W),
    toState (F.map h s) = (toState s).restrict V W h

/-- StateSheaf has a canonical projection -/
instance : HasStateProjection StateSheaf.presheaf where
  toState := Section.toUIState
  toState_restrict := by
    intro W V h s
    rfl  -- Definitional for StateSheaf

/-- Lift a UIState to a section of any presheaf with state projection -/
def UIState.toSectionGeneral {F : UIPresheaf} [HasStateProjection F]
    (s : UIState) (W : FrameWindow) : Section F W :=
  sorry  -- Requires inverse of the projection, not always possible


/-- Valid UI state for a frame window: state must be consistent with events -/
structure ValidUIState (W : FrameWindow) where
  state : UIState
  -- State is replayable from W's events
  is_valid : ∃ (replay : ReplayFunction), replay.replay W.events = state

/-- The canonical state presheaf assigns valid UI states to each frame window -/
def StateSheaf : Sheaf where
  presheaf := {
    obj := fun W => ValidUIState W
    map := fun {F G} (h : F ≤ G) s => {
      state := s.state.restrict F G h
      is_valid := by
        obtain ⟨replay, hrep⟩ := s.is_valid
        use replay
        -- Restriction commutes with replay by replay_respects_restriction
        rw [← hrep]
        exact replay_respects_restriction replay h
    }
    map_id := by
      intro W
      ext s
      simp [UIState.restrict]
    map_comp := by
      intro F G H hFG hGH
      ext s
      simp [UIState.restrict]
  }
  is_sheaf := by
    -- StateSheaf is a sheaf by construction from replay determinism
    intro W cover sections compat
    constructor
    · -- Existence: glue via unionEvents
      let allEvents := unionEvents cover
      -- Assume we have a deterministic replay function
      -- (This is what FrameDeterministic guarantees)
      sorry  -- Need: global replay function from determinism
    · -- Uniqueness: unique replay from events
      intro s1 s2 hs1 hs2
      -- Both come from replaying the same events
      sorry  -- Follows from FrameDeterministic

/-- Canonical embedding: UIState → Section StateSheaf W

For a state to be a valid section, it must come from replay.
-/
def CoercionToSection (s : UIState) (W : FrameWindow)
    (h_valid : ∃ replay, replay.replay W.events = s) :
    Section StateSheaf.presheaf W :=
  {
    state := s
    is_valid := h_valid
  }

/-- Section.fromReplay for StateSheaf (canonical and definitional) -/
def Section.fromReplay (replay : ReplayFunction) (W : FrameWindow) :
    Section StateSheaf.presheaf W :=
  {
    state := replay.replay W.events
    is_valid := ⟨replay, rfl⟩  -- Definitionally valid
  }

/-- For general presheaves, fromReplay requires embedding from StateSheaf -/
def Section.fromReplayGeneral {F : UIPresheaf} [HasStateProjection F]
    (replay : ReplayFunction) (W : FrameWindow) : Section F W :=
  -- This is only possible if F has a way to embed UIStates
  -- For the main theorem, we work with StateSheaf directly
  sorry

/-- A family of sections over a cover is compatible if restrictions to
intersections agree -/
def CompatibleSections (F : UIPresheaf) {W : FrameWindow} (cover : CoverFamily W)
    (sections : ∀ G ∈ cover.frames, Section F G) : Prop :=
  ∀ (i j : Fin cover.frames.length) (hi : cover.frames[i]'(by sorry) ∈ cover.frames)
    (hj : cover.frames[j]'(by sorry) ∈ cover.frames),
    -- On intersection, the sections must agree
    -- This is simplified; proper version uses pullbacks
    True  -- Placeholder

/-- Gluing of compatible sections to a global section -/
def glue (F : UIPresheaf) {W : FrameWindow} (cover : CoverFamily W)
    (sections : ∀ G ∈ cover.frames, Section F G)
    (compat : CompatibleSections F cover sections) : Section F W :=
  sorry  -- Constructive gluing

/-! ### Sheaf Condition -/

/-- A presheaf is a sheaf if:
1. Compatible families have a unique gluing
2. The gluing restricts back to the original sections

Mathematical formulation: The gluing map is a bijection between
compatible sections on covers and global sections.
-/
def IsSheaf (F : UIPresheaf) : Prop :=
  ∀ (W : FrameWindow) (cover : CoverFamily W)
    (sections : ∀ G ∈ cover.frames, Section F G)
    (compat : CompatibleSections F cover sections),
    -- Existence: can glue
    (∃ s : Section F W, ∀ G (hG : G ∈ cover.frames),
      F.map (cover.subframes G hG) s = sections G hG) ∧
    -- Uniqueness: gluing is unique
    (∀ s1 s2 : Section F W,
      (∀ G (hG : G ∈ cover.frames), F.map (cover.subframes G hG) s1 = sections G hG) →
      (∀ G (hG : G ∈ cover.frames), F.map (cover.subframes G hG) s2 = sections G hG) →
      s1 = s2)

/-! ### Sheaf Type -/

/-- A sheaf is a presheaf satisfying the sheaf condition -/
structure Sheaf where
  presheaf : UIPresheaf
  is_sheaf : IsSheaf presheaf

namespace Sheaf

/-- Constant sheaf (trivially satisfies gluing) -/
def const (S : Type u) : Sheaf where
  presheaf := UIPresheaf.const S
  is_sheaf := by
    intro W cover sections compat
    constructor
    · -- Existence: take any section value (all are the same)
      sorry
    · -- Uniqueness: trivial since restriction is identity
      sorry

end Sheaf

end CondensedTEL
