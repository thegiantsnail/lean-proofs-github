/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.
Authors: TEL Development Team

## Frame Windows for UI Observation

Frame windows represent temporal intervals during which UI events are observed.
They form the basis for a Grothendieck topology where:
- Objects are frame windows (time intervals with buffer semantics)
- Morphisms are restrictions (subframe inclusions)
- Covers are overlapping frame sequences that tile an observation period

### Mathematical Structure

A frame window `F` is characterized by:
- Time interval `[start, end]`
- Frame rate (frames per second)
- Buffer capacity
- Event log (sequence of UI events)

Frame windows form a poset under the subframe relation, which induces
a topology suitable for sheaf theory.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Order.CompleteLattice

universe u v

namespace CondensedTEL

/-! ### Time representation -/

/-- Time measured in milliseconds since epoch -/
def Time : Type := ℕ

/-- Time has a natural ordering from ℕ -/
instance : LE Time := inferInstanceAs (LE ℕ)

/-- Time has less-than from ℕ -/
instance : LT Time := inferInstanceAs (LT ℕ)

/-- Time has a maximum operation -/
instance : Max Time := inferInstanceAs (Max ℕ)

/-- Time has a minimum operation -/
instance : Min Time := inferInstanceAs (Min ℕ)

/-- Time has decidable equality -/
instance : DecidableEq Time := inferInstanceAs (DecidableEq ℕ)

/-- Time comparisons are decidable -/
instance (a b : Time) : Decidable (a ≤ b) := Nat.decLe a b

/-- Time intervals are pairs (start, end) where start ≤ end -/
structure TimeInterval where
  start : Time
  finish : Time
  valid : start ≤ finish

namespace TimeInterval

instance : LE TimeInterval where
  le I J := I.start ≥ J.start ∧ I.finish ≤ J.finish

instance : PartialOrder TimeInterval where
  le := (· ≤ ·)
  le_refl I := ⟨Nat.le_refl _, Nat.le_refl _⟩
  le_trans := by
    intro I J K hIJ hJK
    exact ⟨Nat.le_trans hJK.1 hIJ.1, Nat.le_trans hIJ.2 hJK.2⟩
  le_antisymm := by
    intro I J hIJ hJI
    cases I with | mk start1 finish1 valid1 =>
    cases J with | mk start2 finish2 valid2 =>
    simp at hIJ hJI
    have hs : start1 = start2 := Nat.le_antisymm hJI.1 hIJ.1
    have hf : finish1 = finish2 := Nat.le_antisymm hIJ.2 hJI.2
    subst hs hf
    rfl

/-- Intersection of time intervals (may be empty) -/
def intersect (I J : TimeInterval) : Option TimeInterval :=
  let start := max I.start J.start
  let finish := min I.finish J.finish
  if h : start ≤ finish then
    some ⟨start, finish, h⟩
  else
    none

/-- Two intervals overlap if their intersection is non-empty -/
def overlaps (I J : TimeInterval) : Prop :=
  (intersect I J).isSome

/-- If I ≤ J, then any timestamp in I is also in J -/
lemma mem_of_mem_of_le {I J : TimeInterval} (h : I ≤ J) {t : Time} :
    (I.start ≤ t ∧ t ≤ I.finish) → (J.start ≤ t ∧ t ≤ J.finish) := by
  intro ht
  -- I ≤ J means I.start ≥ J.start ∧ I.finish ≤ J.finish
  rcases h with ⟨hs, hf⟩
  constructor
  · -- J.start ≤ I.start ≤ t
    exact Nat.le_trans hs ht.1
  · -- t ≤ I.finish ≤ J.finish
    exact Nat.le_trans ht.2 hf

end TimeInterval

/-! ### UI Events -/

/-- Abstract UI event type (parameterized) -/
inductive UIEvent
  | mouseClick (x y : ℕ) (timestamp : Time)
  | keyPress (key : String) (timestamp : Time)
  | scroll (dx dy : ℤ) (timestamp : Time)
  | custom (data : String) (timestamp : Time)

namespace UIEvent

/-- Extract timestamp from any event -/
def timestamp : UIEvent → Time
  | mouseClick _ _ t => t
  | keyPress _ t => t
  | scroll _ _ t => t
  | custom _ t => t

end UIEvent

/-! ### Frame Windows -/

/-- A frame window is a time interval with associated UI events and rendering state.

Frame windows are the objects of our site. They represent observable units where:
- UI state can be deterministically reconstructed from events
- Rendering is consistent within the frame
- State can be restricted to subframes
-/
structure FrameWindow where
  /-- Time interval covered by this frame -/
  interval : TimeInterval
  /-- Frame rate in FPS -/
  frameRate : ℕ
  /-- UI events occurring in this window -/
  events : List UIEvent
  /-- All events are within the time interval -/
  events_in_interval : ∀ e ∈ events,
    interval.start ≤ e.timestamp ∧ e.timestamp ≤ interval.finish
  /-- Events are sorted by timestamp -/
  events_sorted : events.Chain' (fun e1 e2 => e1.timestamp ≤ e2.timestamp) := by decide

namespace FrameWindow

/-- Helper predicate for event filtering (decidable version) -/
def eventInInterval (I : TimeInterval) (e : UIEvent) : Bool :=
  decide (I.start ≤ e.timestamp ∧ e.timestamp ≤ I.finish)

/-- Predicate saying G is the restriction of W to G.interval -/
def IsRestriction (G W : FrameWindow) : Prop :=
  G.interval ≤ W.interval ∧
  G.frameRate = W.frameRate ∧
  G.events = W.events.filter (eventInInterval G.interval)

/-- Subframe relation: G is a restriction of W -/
instance : LE FrameWindow where
  le G W := IsRestriction G W

/-- Frame windows form a preorder under restriction -/
instance : Preorder FrameWindow where
  le := (· ≤ ·)
  le_refl W := by
    refine ⟨⟨Nat.le_refl _, Nat.le_refl _⟩, rfl, ?_⟩
    -- filter over full interval gives same list
    have : W.events.filter (eventInInterval W.interval) = W.events := by
      apply List.filter_eq_self.mpr
      intro e he
      simp only [eventInInterval]
      rw [decide_eq_true_iff]
      exact W.events_in_interval e he
    exact this.symm
  le_trans := by
    intro A B C hAB hBC
    rcases hAB with ⟨hIAB, hfpsAB, hevAB⟩
    rcases hBC with ⟨hIBC, hfpsBC, hevBC⟩
    refine ⟨?_, ?_, ?_⟩
    · -- interval trans
      constructor
      · exact Nat.le_trans hIBC.1 hIAB.1
      · exact Nat.le_trans hIAB.2 hIBC.2
    · -- frameRate trans
      exact hfpsAB.trans hfpsBC
    · -- events: filter-of-filter collapses
      calc A.events
          = B.events.filter (eventInInterval A.interval) := hevAB
          _ = (C.events.filter (eventInInterval B.interval)).filter (eventInInterval A.interval) := by rw [hevBC]
          _ = C.events.filter (eventInInterval A.interval) := by sorry  -- TODO: Filter composition

/-- Frame windows form a partial order under restriction -/
instance : PartialOrder FrameWindow where
  le := (· ≤ ·)
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans
  le_antisymm := by
    intro A B hAB hBA
    rcases hAB with ⟨hIAB, hfpsAB, hevAB⟩
    rcases hBA with ⟨hIBA, hfpsBA, hevBA⟩
    -- interval equality using TimeInterval's PartialOrder
    have hInt : A.interval = B.interval := le_antisymm hIAB hIBA
    -- frameRate equality
    have hFps : A.frameRate = B.frameRate := hfpsAB
    -- events equality
    have hEv : A.events = B.events := by
      calc A.events
          = B.events.filter (eventInInterval A.interval) := hevAB
          _ = B.events.filter (eventInInterval B.interval) := by rw [hInt]
          _ = B.events := by
              -- filter with same interval is identity
              apply List.filter_eq_self.mpr
              intro e he
              simp only [eventInInterval]
              rw [decide_eq_true_iff]
              exact B.events_in_interval e he
    -- structural equality
    cases A with | mk iA fA eA hA hsA =>
    cases B with | mk iB fB eB hB hsB =>
    simp only at hInt hFps hEv
    cases hInt
    cases hFps
    cases hEv
    rfl

/-- Restriction of a frame window to a subinterval -/
def restrict (F : FrameWindow) (I : TimeInterval) (h : I ≤ F.interval) : FrameWindow where
  interval := I
  frameRate := F.frameRate
  events := F.events.filter (eventInInterval I)
  events_in_interval := by
    intro e he
    simp only [List.mem_filter, eventInInterval] at he
    have := he.2
    simp only [decide_eq_true_iff] at this
    exact this
  events_sorted := by
    -- Filtering preserves sortedness
    have : IsTrans UIEvent (fun e1 e2 => e1.timestamp ≤ e2.timestamp) := ⟨fun _ _ _ => Nat.le_trans⟩
    exact List.Chain'.sublist F.events_sorted (List.filter_sublist _)

/-- restrict produces a proper subframe -/
lemma restrict_le (F : FrameWindow) (I : TimeInterval) (h : I ≤ F.interval) :
    restrict F I h ≤ F := by
  -- By definition of IsRestriction
  exact ⟨h, rfl, rfl⟩

/-- Two frame windows overlap if their time intervals overlap -/
def overlaps (F G : FrameWindow) : Prop :=
  F.interval.overlaps G.interval

/-- The intersection frame (when it exists) -/
def intersect (F G : FrameWindow) (h : F.overlaps G) : FrameWindow :=
  let start := max F.interval.start G.interval.start
  let finish := min F.interval.finish G.interval.finish
  have hvalid : start ≤ finish := by sorry  -- TODO: Derive from overlaps
  F.restrict ⟨start, finish, hvalid⟩ (by
    constructor
    · exact Nat.le_max_left _ _
    · exact Nat.min_le_left _ _)

/-- The intersection is a restriction of the left frame -/
lemma intersect_le_left (F G : FrameWindow) (h : F.overlaps G) : intersect F G h ≤ F := by
  unfold intersect
  exact restrict_le _ _ _

end FrameWindow

/-! ### Extremally Disconnected Property -/

/-- A frame window is extremally disconnected (ED) if every open set's closure is open.
For frame windows, this corresponds to "clean frame boundaries": events don't span
frame boundaries, and all state transitions complete within the frame.
-/
def FrameWindow.isExtremallyDisconnected (F : FrameWindow) : Prop :=
  ∀ e ∈ F.events, F.interval.start < e.timestamp ∧ e.timestamp < F.interval.finish →
    -- No events on boundaries (excluding endpoints ensures clean separation)
    e.timestamp ≠ F.interval.start ∧ e.timestamp ≠ F.interval.finish

/-! ### Site Structure -/

/-- A covering family for a frame window F is a collection of subframes
that "cover" F in the sense that every event in F appears in some cover member.

This is the covering relation for our Grothendieck topology.
-/
structure CoverFamily (F : FrameWindow) where
  /-- The covering frames -/
  frames : List FrameWindow
  /-- Covers must be non-empty (every frame is covered by at least itself) -/
  frames_nonempty : frames ≠ []
  /-- Each covering frame is a subframe of F -/
  subframes : ∀ G ∈ frames, G ≤ F
  /-- Every event in F appears in some cover -/
  event_coverage : ∀ e ∈ F.events, ∃ G ∈ frames, e ∈ G.events
  /-- Frames don't duplicate events (each event appears in at most one frame) -/
  frames_disjoint : ∀ e G1 G2, G1 ∈ frames → G2 ∈ frames → e ∈ G1.events → e ∈ G2.events → G1 = G2
  /-- Frames are arranged with temporally compatible events.
      This ensures that when concatenating events from frames via bind,
      the result maintains timestamp ordering. -/
  frames_temporally_ordered : frames.Chain' (fun G1 G2 =>
    ∀ e1 ∈ G1.events, ∀ e2 ∈ G2.events, e1.timestamp ≤ e2.timestamp)

namespace CoverFamily

/-- If an event is in a subframe's events, it's in the parent frame's events -/
lemma events_subset_of_subframe {W G : FrameWindow} (hG : G ≤ W)
    {e : UIEvent} (he : e ∈ G.events) : e ∈ W.events := by
  -- G ≤ W means G.events is a filter of W.events
  rcases hG with ⟨_, _, hevents⟩
  rw [hevents] at he
  exact List.mem_of_mem_filter he

/-- The identity cover (F covers itself) -/
def id (F : FrameWindow) : CoverFamily F where
  frames := [F]
  subframes := by intro G hG; simp at hG; subst hG; exact le_refl _
  event_coverage := by intro e he; exact ⟨F, by simp, he⟩
  frames_temporally_ordered := by simp [List.Chain']
  frames_nonempty := by simp
  frames_disjoint := by
    -- Single frame covers: trivially disjoint (events only in [F])
    intro e G₁ G₂ hG₁ hG₂
    simp at hG₁ hG₂
    subst hG₁; subst hG₂
    simp

/-- Pullback of a cover along a morphism (restriction) -/
def pullback {F G : FrameWindow} (cover : CoverFamily G) (h : F ≤ G) : CoverFamily F where
  frames := cover.frames.map (fun H => F.intersect H (by sorry))  -- TODO: Prove F and H overlap
  subframes := by
    intro H' hH'
    simp only [List.mem_map] at hH'
    rcases hH' with ⟨H, hH, rfl⟩
    -- intersect F H ≤ F
    exact FrameWindow.intersect_le_left F H _
  event_coverage := by sorry  -- TODO: Event coverage
  frames_temporally_ordered := by sorry  -- TODO: Temporal ordering
  frames_nonempty := by
    -- cover.frames ≠ [] (by assumption) → map is nonempty
    simp [List.map_eq_nil]
    exact cover.frames_nonempty
  frames_disjoint := by sorry  -- TODO: Pullback preserves disjointness

/-- Composition of covers (transitivity) -/
noncomputable def compose {F : FrameWindow} (cover1 : CoverFamily F)
    (cover2 : ∀ G ∈ cover1.frames, CoverFamily G) : CoverFamily F where
  frames := cover1.frames.bind (fun G =>
    haveI : Decidable (G ∈ cover1.frames) := Classical.propDecidable _
    if hG : G ∈ cover1.frames then (cover2 G hG).frames else [])
  subframes := by sorry  -- TODO: Transitivity of restrictions
  event_coverage := by sorry  -- TODO: Composition coverage
  frames_temporally_ordered := by sorry  -- TODO: Bind preserves ordering
  frames_nonempty := by sorry  -- TODO: Composition preserves nonemptiness
  frames_disjoint := by sorry  -- TODO: Composition preserves disjointness

end CoverFamily

/-! ### Grothendieck Topology -/

/-- The site of frame windows with the coverage given by overlapping frame families.

This is the fundamental topological structure for TEL UI observations.
Key property: Extremally disconnected covers form a basis and serve as projective generators.
-/
def FrameWindow.site : Type := FrameWindow

-- TODO: Define actual Grothendieck site structure using mathlib's CategoryTheory.Sites
-- This requires:
-- 1. Category instance for FrameWindow
-- 2. Grothendieck topology with CoverFamily as covering sieves
-- 3. Proof of coverage axioms (pullback stability, transitivity)

end CondensedTEL
