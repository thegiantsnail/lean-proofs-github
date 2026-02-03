# Concrete Examples and Axiom Proofs

This directory contains **concrete operational models** that instantiate the abstract structures from the universal equivalence pattern, demonstrating that the axioms are **provable** from first principles, not merely reasonable assumptions.

## Files

### DiscreteCounter.lean ⭐ **NEW**

**Status**: In progress (base definitions complete, main proof in development)

**Purpose**: Prove the **functoriality axiom** from Theorem 1 (Sheaf ↔ Frame Determinism) using a concrete discrete-time counter model.

**Model**:
- **State**: Temporal trace `ℕ → ℕ` (timestep → counter value)
- **Events**: Increment, Decrement, Reset at discrete timesteps
- **Replay**: Pure functional fold over events
- **Restriction**: Filter events by time interval, restrict state domain

**Main Result**:
```lean
theorem replay_respects_restriction :
  replayDiscrete (restrictEvents events V) =
  restrictState (replayDiscrete (restrictEvents events W)) V
```

**Scientific Impact**: This validates that Axiom 1 (functoriality) is not just axiomatized but is **derivable** from concrete operational semantics, strengthening the meta-theorem's empirical foundation.

**Proof Strategy**: Induction on sorted event list, showing fold commutes with restriction.

**Timeline**: 
- Phase 1 (✅ Complete): Model definitions, basic properties
- Phase 2 (⏳ In progress): Main theorem proof
- Phase 3 (Planned): Examples and computational verification

## Planned Future Files

### ContinuousCounter.lean
- Generalize discrete model to continuous time ℝ
- Connect to existing FrameWindow infrastructure
- Prove functoriality in continuous setting

### CompletenessProof.lean
- Prove the completeness axiom (gluing property)
- Show local replays on covering intervals determine global replay
- Validate second axiom from operational semantics

### ComputationalContent.lean
- Prove the computational content axiom (decidability)
- Show replay correspondence is constructively checkable
- Validate third axiom from operational semantics

## Impact on Paper

With `DiscreteCounter.lean` complete, the workshop paper can claim:

> "We prove the functoriality axiom from first principles using a concrete operational semantics (Appendix B), demonstrating that our axiomatization is not merely plausible but **provably derivable** from computational models."

This significantly strengthens the paper's scientific rigor beyond pure axiomatization.

## Building

```bash
lake build CondensedTEL.Examples.DiscreteCounter
```

## Testing

Run the examples:
```bash
lake env lean CondensedTEL/Examples/DiscreteCounter.lean
```

## Timeline

- **Today**: Complete Phase 1 (definitions) ✅
- **Tomorrow**: Complete Phase 2 (main proof)
- **Day 3**: Add to paper, submit with proven axiom

**Total effort**: 5-7 hours for proven axiom (vs. mere axiomatization)
**Scientific gain**: Massive (provable > plausible)
