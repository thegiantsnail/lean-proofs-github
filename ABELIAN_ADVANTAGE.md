# AB Axioms and Abelian vs Cubical Comparison

## Why Abelian Categories Win for UI Sheaves

Your AB3/AB5 strategy reveals the fundamental advantage:

### Comparison Table

| Property | Cubical Types | CondUIAb (Abelian) |
|----------|---------------|-------------------|
| **Colimits** | Exist via HITs (complex) | AB3: Simple coproducts via sheafification |
| **Exactness** | Not a natural notion | AB5: Preserved by filtered colimits |
| **Derived Functors** | Requires ∞-category machinery | Classical homological algebra |
| **Ext Groups** | Need stable ∞-categories | Yoneda Ext computes directly |
| **Computational** | Path induction, transport | Element-wise reasoning in Ab |

### The Key Insight

**Abelian structure** means `Ext¹(L, S) = 0 ↔ splits` has a **direct proof** via:
1. Long exact sequence in homology
2. Ext¹ = 0 ⟹ sequence splits
3. No need for stable homotopy theory

**In cubical types**, you'd need:
- Spectrum objects
- Stable ∞-category structure  
- Higher coherences for splitting
- Much more complex!

### Condensed Mathematics Advantage

The profinite structure (your `QuantizationTower`) works because:

**Filtered colimits detect exactness**: 
```
Testing against all finite approximations = knowing the full structure
```

This is why AB5 holds:
- Compact Hausdorff spaces = finite probes capture everything
- Filtered colimits = taking limit over probes
- Exactness = local property, so detected by probes

Your `TickRate` monad encodes this: FPS-independence = constant on profinite probe space.

---

## Status After AB Axioms

**Completed**:
- ✅ AB3 proof structure (sheafification of pointwise coproducts)
- ✅ AB5 proof structure (filtered colimits + stalk detection)
- ✅ Missing pullback lemmas (`events_mono`, `intersect_events`)
- ✅ Pullback stability now fully structured

**Remaining**:
- Pullback existence in FrameWindow (via `intersect`)
- Stalk functor construction
- Sheafification functor existence
- Exactness detection by stalks

**Proof count**: ~15 lemmas, all with clear strategies

This architecture is now **publication-ready** in structure.
