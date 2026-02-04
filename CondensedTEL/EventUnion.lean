/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.

## Event Union for Backward Direction

Canonical event union from cover families, needed for the
backward direction of the sheaf-determinism equivalence.
-/

import CondensedTEL.FrameWindow
import Mathlib.Data.List.Sort

namespace CondensedTEL

/-! ### Event Union -/

/-- Merge events from all frames in a cover.
Uses sorted list union to avoid multiset quotienting. -/
def unionEvents (cover : CoverFamily W) : EventSequence :=
  -- Flatten all events from cover members
  let allEvents := cover.frames.bind (fun F => F.events)
  -- Sort by timestamp to ensure canonical ordering
  allEvents.mergeSort (fun e1 e2 => e1.timestamp ≤ e2.timestamp)

/-- Union contains all events from each cover member -/
lemma event_in_union_of_mem_cover {W : FrameWindow} (cover : CoverFamily W)
    (F : FrameWindow) (hF : F ∈ cover.frames) (e : UIEvent) (he : e ∈ F.events) :
    e ∈ unionEvents cover := by
  unfold unionEvents
  sorry  -- e ∈ allEvents by hF, preserved by mergeSort

/-- Union events are sorted by timestamp -/
lemma unionEvents_sorted {W : FrameWindow} (cover : CoverFamily W) :
    EventSequence.isSorted (unionEvents cover) := by
  unfold unionEvents EventSequence.isSorted
  sorry  -- mergeSort produces sorted list

/-- Permutation invariance: sorted lists with same elements give same replay -/
lemma replay_permutation_invariant (replay : ReplayFunction) 
    (seq1 seq2 : EventSequence) 
    (h_equiv : EventSequence.equiv seq1 seq2)
    (h_sorted1 : seq1.isSorted) (h_sorted2 : seq2.isSorted) :
    replay.replay seq1 = replay.replay seq2 :=
  replay.sorted_equiv h_sorted1 h_sorted2 h_equiv

end CondensedTEL
