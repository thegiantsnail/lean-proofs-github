# Blueprint Quick Reference

**For**: TEL Lean Formalization  
**Updated**: February 1, 2026

## 🎯 Main Results

| Label | Theorem | Status | Priority |
|-------|---------|--------|----------|
| `thm:sheaf-iff-deterministic` | **IsSheaf ↔ FrameDeterministic** | ⬜ sorry | 🔴 HIGHEST |
| `thm:ext1-vanishes` | SES splits ↔ Ext¹ = 0 | ⬜ sorry | 🟠 High |
| `thm:h1-is-z2` | H₁(Quine) ≅ ℤ² | ⬜ sorry | 🟠 High |
| `thm:ed-acyclicity` | H¹(ED frame) = 0 | ⬜ sorry | 🟡 Medium |
| `thm:quine-is-solid` | Quines are solid | ⬜ sorry | 🟡 Medium |
| `thm:certificates-are-condensed` | Certificates lift to Cond(Ab) | ⬜ sorry | 🟢 Low |

## 📁 File Map

| Concept | Lean File | Lines |
|---------|-----------|-------|
| Frame Windows | `CondensedTEL/FrameWindow.lean` | ~400 |
| Sheaf ↔ Determinism | `CondensedTEL/FrameDeterministic.lean` | 397 |
| Solid/Liquid | `CondensedTEL/SolidKernel.lean` | 148 |
| Ext¹ Theory | `CondensedTEL/ExtObstruction.lean` | - |
| Quines | `CondensedTEL/QuineCondensed.lean` | 252 |
| Langlands | `CondensedTEL/CondensedLanglands.lean` | - |

## 🔍 Key Definitions

```lean
-- Frame Window (temporal observation interval)
structure FrameWindow where
  start : ℝ
  finish : ℝ
  h : start ≤ finish

-- Frame Deterministic (computational property)
def FrameDeterministic (replay : ReplayFunction) : Prop :=
  ∀ (W : FrameWindow) (cover : CoverFamily W),
    ∃! globalState : UIState, ...

-- Sheaf Condition (gluing property)
def IsSheaf (F : UIPresheaf) : Prop := ...

-- Central Theorem
theorem sheaf_iff_deterministic (replay : ReplayFunction) :
    IsSheaf F ↔ FrameDeterministic replay := by sorry
```

## 🎨 Dependency Structure

```
FrameWindow → Coverage → ED Property → ED Acyclicity
                    ↓
UIPresheaf → IsSheaf → [Sheaf ↔ Determinism] ⭐
                           ↑
                  FrameDeterministic

Solid → SES Decomposition → Ext¹ Vanishing
Liquid ↗

QuineH1 → H₁=ℤ² → Quine Solidity
           ↘
         CondensedQuine → Quine Tower
```

## 🚀 Proof Strategy

### Phase 1: Core (Week 1-2)
1. Forward direction: IsSheaf → FrameDeterministic
2. Backward direction: FrameDeterministic → IsSheaf
3. Ext¹ vanishing theorem

### Phase 2: Topology (Week 3)
4. H₁ = ℤ² from empirical data
5. ED acyclicity

### Phase 3: Integration (Week 4)
6. Quine solidity
7. Certificates condensed

## 📊 Current Status

- **Total Theorems**: 6
- **Proved**: 0
- **In Progress**: Annotations prepared
- **Next Target**: `thm:sheaf-iff-deterministic`

## 📖 Documentation

- **Full Blueprint**: `blueprint/BLUEPRINT.md` (comprehensive)
- **LaTeX Version**: `blueprint/condensed_tel.tex` (for PDF)
- **This File**: Quick reference for daily work

## 💡 Tips

1. **Start with forward direction** of main theorem
2. **Use `replay_respects_restriction`** axiom
3. **Reference empirical data** for H₁ = ℤ²
4. **Check STATUS.md** for proof tactics
5. **See Examples/** for concrete instances

## 🔗 Key Files

- Main theorem: [FrameDeterministic.lean:344](../CondensedTEL/FrameDeterministic.lean#L344)
- Forward proof: [FrameDeterministic.lean:180](../CondensedTEL/FrameDeterministic.lean#L180)
- Backward proof: [FrameDeterministic.lean:262](../CondensedTEL/FrameDeterministic.lean#L262)

---

**Quick Access**: Keep this file open while working on proofs!
