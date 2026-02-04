# Sheaf-Determinism Proof - Work in Progress

**Date**: January 4, 2026  
**Status**: Core structure complete, 5 lemmas remain

## Overview

We have successfully structured the proof of the main TEL theorem:

**IsSheaf StateSheaf.presheaf ↔ FrameDeterministic**

This establishes the equivalence between:
- **Sheaf condition** (categorical/topological): Compatible local sections uniquely glue to a global section
- **Frame determinism** (computational): UI state is uniquely determined by event sequences

## Files Created/Modified

### New Files
1. **`SheafDeterminismTheorem.lean`** - Clean, focused proof of the main theorem
   - Forward direction: `sheaf_implies_deterministic`
   - Reverse direction: `deterministic_implies_sheaf`
   - Main result: `sheaf_iff_frame_deterministic`

### Modified Files
1. **`FrameDeterministic.lean`** - Added helper functions
   - `EventSequence.unionFromCover`
   - `EventSequence.restrictTo`
   - `Section.fromReplay`
   - Updated `FrameDeterministic` definition (cleaner)

2. **`UIPresheaf.lean`** - Added lifting infrastructure
   - `UIState.toSection` / `Section.toUIState`
   - `HasStateProjection` typeclass
   - Better integration with `StateSheaf`

3. **`CondensedTEL.lean`** - Added import for new theorem file

## Proof Structure

### Forward Direction: Sheaf → Deterministic

```
Given: IsSheaf StateSheaf.presheaf
Goal: FrameDeterministic replay

Strategy:
1. For any cover {Gᵢ} of W, construct sections via replay on each Gᵢ
2. Show sections are compatible (via replay_respects_restriction)
3. Apply sheaf gluing → unique global section
4. Extract UIState → this is the unique deterministic state
```

**Status**: ✅ Structure complete, 2 sorries remain
- `state_from_compatible_restrictions` (main lemma)
- Connection between compatibility and replay equivalence

### Reverse Direction: Deterministic → Sheaf

```
Given: FrameDeterministic replay
Goal: IsSheaf StateSheaf.presheaf

Strategy:
1. Given compatible sections {sᵢ} over cover {Gᵢ}
2. Apply frame determinism → unique global state
3. Show this state forms a valid section
4. Verify it restricts correctly (from determinism)
5. Uniqueness follows directly from determinism
```

**Status**: ✅ Structure complete, 3 sorries remain
- Proof that deterministic state is valid (comes from replay W.events)
- Connection between sections and replay
- Extraction of restriction conditions

## Remaining Work

### Priority 1: Core Lemmas (2-3 hours)

1. **`state_from_compatible_restrictions`**
   - Needs: Event coverage lemma
   - Needs: `W.events ≃ unionFromCover cover`
   - This is the key technical lemma

2. **Section-replay correspondence**
   - Show: compatible sections ↔ sections from replay
   - Currently using sorry in several places

### Priority 2: Event Coverage (1-2 hours)

3. **`event_coverage_union`**
   - Prove: `∀ e ∈ W.events, e ∈ unionFromCover cover`
   - Follows from `CoverFamily.event_coverage`

4. **`replay_union_equals_state`**
   - Prove: `replay (unionFromCover cover) = replay W.events`
   - Uses `replay.sorted_equiv`

### Priority 3: Validity Proofs (1 hour)

5. **`deterministic_state_valid`**
   - Show: state from frame determinism comes from replay W.events
   - Should follow from definition of `FrameDeterministic`

## Key Insights

### Why This Works

1. **StateSheaf is the right presheaf**: It has canonical UIState extraction/lifting
2. **ValidUIState encodes replay**: Validity = ∃ replay such that...
3. **Frame determinism IS the sheaf condition**: Just expressed operationally

### Proof Architecture

```
FrameDeterministic: ∀ W cover, ∃! state, ∀ G ∈ cover,
                    replay G.events = state.restrict G W

IsSheaf: ∀ W cover sections compat, ∃! section, ∀ G ∈ cover,
         section.restrict G W = sections[G]
```

The correspondence:
- `state` ↔ `section.toState`
- `replay G.events` ↔ `sections[G].toState`
- `state.restrict` ↔ `section.restrict`

## Testing Plan

Once the 5 sorries are filled:

1. **Compilation test**
   ```
   lake build CondensedTEL.SheafDeterminismTheorem
   ```

2. **Import test**
   ```lean
   import CondensedTEL.SheafDeterminismTheorem
   
   #check sheaf_iff_frame_deterministic
   ```

3. **Usage test**: Apply to concrete examples
   - Counter replay (should be deterministic)
   - Animation replay (should be non-deterministic)

## Next Steps

1. ✅ Create clean proof structure (DONE)
2. ⏳ Fill 5 remaining lemmas (IN PROGRESS)
3. ⏳ Test compilation
4. ⏳ Write proof documentation
5. ⏳ Connect to Python via extraction

## Notes

- **Lean version**: Lean 4 (compatible with existing codebase)
- **Dependencies**: Mathlib4 (CategoryTheory, Topology)
- **Lines of code**: ~250 (new theorem file)
- **Proof complexity**: Medium (structure is simple, details require careful type management)

## Questions for Review

1. Should we add more intermediate lemmas to break down the sorries?
2. Do we need explicit proofs of event coverage properties?
3. Should we add a tactic for automation of restriction reasoning?

---

**Summary**: The proof architecture is solid. We have 5 well-isolated lemmas that need to be proved. Each lemma has a clear mathematical content and should be provable with existing infrastructure. Estimated time to complete: 4-6 hours.
