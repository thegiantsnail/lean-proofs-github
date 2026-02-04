# Quick Start: LeanArchitect Migration for TEL

This guide gets you started with LeanArchitect integration in **under 30 minutes**.

## Prerequisites Check

```bash
# Check Lean version
lean --version  # Should be v4.3.0 or compatible

# Check current directory
cd C:\AI-Local\tel\lean-formalization
ls  # Should see lakefile.lean, CondensedTEL/, etc.
```

## Step 1: Backup Current Work (2 min)

```bash
# Create backup
cd C:\AI-Local\tel
cp -r lean-formalization lean-formalization-backup-$(date +%Y%m%d)

# Or on Windows:
cd C:\AI-Local\tel
xcopy lean-formalization lean-formalization-backup-%date:~-4,4%%date:~-10,2%%date:~-7,2% /E /I /H
```

## Step 2: Add LeanArchitect Dependency (5 min)

### 2.1 Update lakefile.lean

Open `C:\AI-Local\tel\lean-formalization\lakefile.lean` and add the LeanArchitect requirement:

```lean
import Lake
open Lake DSL

package «condensed_tel» where
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

-- ⭐ ADD THIS: LeanArchitect dependency
require Architect from git
  "https://github.com/hanwenzhu/LeanArchitect"

@[default_target]
lean_lib CondensedTEL where
  globs := #[.submodules `CondensedTEL]

-- Your existing executables remain unchanged
lean_exe nullsth where
  root := `CondensedTEL.NullSTHOperational
  supportInterpreter := true

lean_exe contracts where
  root := `CondensedTEL.OperatorContractsCLI
  supportInterpreter := true

lean_exe composed_contracts where
  root := `CondensedTEL.ComposedContractsCLI
  supportInterpreter := true
```

### 2.2 Update Dependencies

```bash
cd C:\AI-Local\tel\lean-formalization
lake update
lake build Architect  # This will download and build LeanArchitect
```

This may take 5-10 minutes the first time.

## Step 3: Create Blueprint Directory (2 min)

```bash
cd C:\AI-Local\tel\lean-formalization
mkdir blueprint
cd blueprint

# Create minimal blueprint document
```

Create `blueprint/condensed_tel.tex` with this minimal starter:

```latex
\documentclass{article}
\usepackage{blueprint}
\usepackage{amsmath, amsthm, amssymb}
\usepackage{hyperref}

\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}

\title{Condensed Mathematics for TEL}
\author{Athena}

\begin{document}
\maketitle

\section{Core Theorems}
\inputleannode{thm:sheaf-iff-deterministic}

\end{document}
```

## Step 4: Annotate Your First Theorem (10 min)

Let's start with the main theorem. Open `CondensedTEL/FrameDeterministic.lean`.

### 4.1 Add Import

At the very top of the file, add:

```lean
import Architect
```

### 4.2 Annotate the Main Theorem

Find this theorem (around line 60):

```lean
theorem sheaf_iff_deterministic (F : UIPresheaf) (replay : ReplayFunction) :
    IsSheaf F ↔ FrameDeterministic replay := by
  sorry
```

Replace it with:

```lean
@[blueprint "thm:sheaf-iff-deterministic"
  (statement := /-- A UI presheaf $F$ is a sheaf if and only if its replay 
    function is frame-deterministic. -/)
  (proof := /-- \textbf{Forward}: Sheaf gluing uniqueness implies replay 
    determinism on overlaps. \textbf{Backward}: Deterministic replay ensures 
    compatible sections glue uniquely. -/)]
theorem sheaf_iff_deterministic (F : UIPresheaf) (replay : ReplayFunction) :
    IsSheaf F ↔ FrameDeterministic replay := by
  sorry
```

### 4.3 Test It

```bash
cd C:\AI-Local\tel\lean-formalization
lake build CondensedTEL.FrameDeterministic
```

If it compiles successfully, you've successfully integrated LeanArchitect! ✅

## Step 5: Generate Blueprint (5 min)

```bash
# Build all blueprint data
lake build :blueprint

# Check generated files
ls .lake/build/blueprint/
# Should see: FrameDeterministic.tex and other generated files
```

### 5.1 Compile Blueprint PDF

```bash
cd blueprint
pdflatex condensed_tel.tex
```

Open `condensed_tel.pdf` - you should see your theorem with automatic `\lean` tags!

## What You've Accomplished

In 30 minutes, you've:

✅ Integrated LeanArchitect into your project
✅ Annotated your first major theorem
✅ Generated a blueprint LaTeX document
✅ Compiled a PDF showing automatic Lean linkage

## Next Steps

### Quick Wins (Next 1-2 hours)

Annotate your other main theorems following the same pattern:

1. **CondensedTEL/SolidKernel.lean**: `ses_splits_iff_ext_vanishes`
2. **CondensedTEL/QuineCondensed.lean**: `universal_quine_H1_Z2`
3. **CondensedTEL/ExtObstruction.lean**: `ext1_iso_cech`

For each:
- Add `import Architect` at top
- Add `@[blueprint "label" (...)]` before theorem
- Rebuild with `lake build CondensedTEL.ModuleName`

### Advanced: Dependency Visualization (After annotations)

Once you've annotated several theorems:

```bash
# Install leanblueprint for web visualization
pip install leanblueprint

# Generate interactive web blueprint
leanblueprint build

# View in browser
# Open blueprint/_build/html/index.html
```

This gives you an interactive dependency graph like the Taylor theorem example in the paper (Figure 2).

### AI-Assisted Proving (Advanced)

After you have the blueprint:

1. **Find leaf nodes**: Theorems with `sorry` but no dependencies on other `sorry` theorems
2. **Use AI**: Pass the formal statement + informal proof to Claude/GPT for tactics
3. **Test and iterate**: Run `lake build` to verify
4. **Track progress**: Blueprint automatically updates colors (blue → green as proofs complete)

## Troubleshooting

### "Cannot find Architect"

**Problem**: Lake can't find LeanArchitect
**Solution**: 
```bash
lake update
lake clean
lake build Architect
```

### "Syntax error in @[blueprint]"

**Problem**: Blueprint attribute not recognized
**Solution**: Make sure `import Architect` is at the very top of your file, before any other imports

### "lake build :blueprint" fails

**Problem**: Blueprint target not found
**Solution**: You may need to add to lakefile.lean:

```lean
-- Add after lean_lib CondensedTEL
package_facet blueprint where
  targets := #[`CondensedTEL]
```

### Blueprint PDF is empty

**Problem**: LaTeX compilation but no content
**Solution**: Make sure you've:
1. Annotated at least one theorem with `@[blueprint]`
2. Built the blueprint with `lake build :blueprint`
3. Used `\inputleannode{your-label}` in the .tex file

## Example: Complete Annotated File

Here's what `CondensedTEL/FrameDeterministic.lean` should look like after migration:

```lean
/-
Copyright (c) 2025 TEL Project. All rights reserved.
Released under Apache 2.0 license.
-/

import Architect  -- ⭐ ADD THIS
import CondensedTEL.FrameWindow
import CondensedTEL.UIPresheaf

namespace CondensedTEL

-- Existing definitions stay the same...

/-- Deterministic replay property for UI states -/
@[blueprint "def:frame-deterministic"  -- ⭐ ADD THIS
  (statement := /-- A replay function is frame-deterministic if running 
    the same event sequence on overlapping frames produces compatible states. -/)]
def FrameDeterministic (replay : ReplayFunction) : Prop :=
  ∀ W₁ W₂ : FrameWindow, ∀ events : EventSequence,
    W₁.start ≤ W₂.start → W₂.start ≤ W₁.finish →
    replay W₁ events = replay W₂ events

/-- The central theorem connecting sheaves to determinism -/
@[blueprint "thm:sheaf-iff-deterministic"  -- ⭐ ADD THIS
  (statement := /-- $\\text{IsSheaf}(F) \\iff \\text{FrameDeterministic}(\\text{replay}_F)$ -/)
  (proof := /-- Forward: gluing uniqueness → replay uniqueness. 
    Backward: deterministic states → sheaf axioms. -/)]
theorem sheaf_iff_deterministic (F : UIPresheaf) (replay : ReplayFunction) :
    IsSheaf F ↔ FrameDeterministic replay := by
  sorry

end CondensedTEL
```

## Resources

- **LeanArchitect GitHub**: https://github.com/hanwenzhu/LeanArchitect
- **LeanArchitect Paper**: See the uploaded PDF for full details
- **Your Project**: `C:\AI-Local\tel\lean-formalization\`
- **Examples**: `C:\AI-Local\tel\lean-formalization\CondensedTEL\Examples\`

## Getting Help

If you encounter issues:

1. **Check the paper**: Section 3 (Methods) has detailed examples
2. **Check LeanArchitect examples**: The MyNat example in the paper (Section A.1)
3. **Lean Zulip**: https://leanprover.zulipchat.com/ (very responsive community)
4. **Your existing STATUS.md**: Documents current proof state

## Summary

**Time investment**: 30 minutes initial setup
**Benefit**: Automatic blueprint generation, progress tracking, AI integration infrastructure
**Risk**: Minimal - you have a backup, changes are additive (just adding `@[blueprint]` tags)

Start with this quick start, then follow the detailed migration plan for complete integration.

Happy formalizing! 🎯
