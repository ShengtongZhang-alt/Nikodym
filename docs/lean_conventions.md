# Lean conventions for this repository

Read this before writing any Lean file here.

## Toolchain and checking

- Lean `v4.33.0-rc1`, Mathlib `v4.33.0-rc1` (pinned; the Mathlib cache is already unpacked in `.lake`).
- Check a single file from the repository root with `lake env lean Nikodym/Path/File.lean`. This is the primary check; it does not write build artifacts.
- Build your own module (and its project dependencies) with `lake build Nikodym.Path.File`. Do not run a bare `lake build` of the whole project while other work is in progress.
- Search Mathlib by grepping `.lake/packages/mathlib/Mathlib`. Prefer `rg -n 'theorem foo' .lake/packages/mathlib/Mathlib`. Use `exact?`, `apply?`, `simp?`, `#check`, `#print axioms` freely while developing, but remove them from the final file.

## File shape

Every file starts with

```lean
/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib            -- or the project modules you need

/-!
# Title

Module docstring: which blueprint nodes this file implements and the main declarations.
-/
```

- Everything lives in `namespace Nikodym` (sub-namespaces are welcome, e.g. `Nikodym.Scaffold`, `Nikodym.MultiQuad`, `Nikodym.LowerBound`).
- Every theorem and definition has a docstring that names the blueprint node it implements, e.g. `/-- Blueprint S02: ... -/`.
- No `sorry`, `admit`, `native_decide`, new `axiom`, or `unsafe` in a finished file. If you cannot close a goal, leave a clearly marked `sorry` with a comment `-- TODO(blueprint XYZ): reason` and report it explicitly.
- Mathlib style: 100-column lines, `fun x ↦ e`, `theorem` for `Prop`, `noncomputable def` where needed, no `autoImplicit`.
- Do not edit files you were not assigned. If you need a lemma from another module that does not exist yet, state it locally as a `private` or clearly named auxiliary lemma in your own file and prove it, or report the gap.
- Do not commit or push; the orchestrator does that.

## Statement discipline

- The blueprint statements are the contract. Keep the same hypotheses; do not add convenience hypotheses (e.g. `Nontrivial`, `DecidableEq`, `0 < n`) unless they are genuinely needed, and if you add one, say so in your report.
- Cardinalities, degrees and exponents live in `ℕ`. Use `ℝ` (`Real.rpow`) only where the blueprint says so.
- Prefer statements that are easy to *use*: explicit `Finset`s over `Set.ncard`, `∀ i, |σ i x| ≤ T` over sup-norms, additive forms over natural subtraction.

## Report format

When done, report: the file path; each blueprint node covered; the exact names and signatures of the public declarations; any remaining `sorry` with the reason; any deviation from the blueprint statement; the output of `lake env lean` on the file (should be clean apart from intended warnings).
