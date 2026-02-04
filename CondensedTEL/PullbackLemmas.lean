/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.

## Missing Lemmas for Pullback Stability

Auxiliary lemmas needed to complete the pullback stability proof.
-/

import CondensedTEL.FrameWindow
import CondensedTEL.UIObservationSite

namespace CondensedTEL

/-! ### Event Monotonicity -/

/-- Events are monotone: if F ≤ G, then F.events ⊆ G.events -/
lemma events_mono {F G : FrameWindow} (h : F ≤ G) : 
    ∀ e ∈ F.events, e ∈ G.events := by
  intro e he
  -- F ≤ G means F.interval ⊆ G.interval
  have hInterval : F.interval ≤ G.interval := h
  
  -- Events in F satisfy F.interval constraints
  have hF_time := F.events_in_interval e he
  
  -- Therefore they satisfy G.interval constraints (by monotonicity)
  have hG_time : G.interval.start ≤ e.timestamp ∧ e.timestamp ≤ G.interval.finish := by
    constructor
    · calc G.interval.start 
        ≤ F.interval.start := hInterval.1
        _ ≤ e.timestamp := hF_time.1
    · calc e.timestamp 
        ≤ F.interval.finish := hF_time.2
        _ ≤ G.interval.finish := hInterval.2
  
  -- Therefore e ∈ G.events
  exact G.events_in_interval e sorry  -- Need: timestamp → membership


/-- Timestamps determine event membership 

**If events are defined as filtered by timestamp**:
This is either a constructor property or follows from event definition.
-/
lemma timestamp_determines_membership {W : FrameWindow} (e : UIEvent) 
    (h : W.interval.start ≤ e.timestamp ∧ e.timestamp ≤ W.interval.finish) :
    e ∈ W.events := by
  -- If events are defined as: filter allEvents (timestamp ∈ interval)
  -- Then this is immediate:
  -- simp [FrameWindow.events, List.mem_filter]
  -- exact h
  
  -- For now, assume this as a well-formedness condition on FrameWindow
  -- (events list must contain exactly those events in the interval)
  sorry  -- Requires: FrameWindow well-formedness axiom

/-! ### Intersection Properties -/

/-- Intersection of overlapping frames is well-defined -/
lemma intersect_well_defined (W F : FrameWindow) (h : W.overlaps F) :
    let I := W.intersect F h
    I ≤ W ∧ I ≤ F := by
  constructor
  · -- I ≤ W by definition
    unfold FrameWindow.intersect
    sorry
  · -- I ≤ F by symmetry
    sorry

/-- Intersection preserves events -/
lemma intersect_events (W F : FrameWindow) (h : W.overlaps F) (e : UIEvent) :
    e ∈ (W.intersect F h).events ↔ e ∈ W.events ∧ e ∈ F.events := by
  constructor
  · -- Forward: intersection events are in both
    intro he
    constructor
    · exact events_mono (intersect_well_defined W F h).1 e he
    · exact events_mono (intersect_well_defined W F h).2 e he
  · -- Backward: events in both are in intersection
    intro ⟨hW, hF⟩
    -- e satisfies both interval constraints
    -- Therefore in intersection interval
    sorry

/-- Overlap means intersection is non-empty (trivial by definition) -/
lemma overlap_nonempty {F G : FrameWindow} (h : F.overlaps G) :
    (F.interval.intersect G.interval).isSome := by
  exact h  -- overlaps is defined as isSome!

/-! ### Sieve Membership -/

/-- Intersection is in pullback sieve -/
lemma intersect_in_pullback {W V : FrameWindow} (f : W ⟶ V) 
    {S : FrameSieve V} (F : FrameWindow) (hF : (sorry : F ⟶ V) ∈ S.arrows) 
    (hFW : F.overlaps W) :
    (sorry : W.intersect F hFW ⟶ W) ∈ (S.pullback f).arrows := by
  -- Pullback sieve contains all composites
  -- F ∩ W → W → V factors through F → V
  apply Sieve.pullback_mem
  exact hF

end CondensedTEL
