## Lean statements

**Status: complete.** Both the lower bound and the construction are proved in
full: the three final theorems in `[Nikodym/Main.lean](Nikodym/Main.lean)`
build without `sorry`, and `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound` for each of them. The formalization plans
are in `[docs/nikodym_bound_lean_blueprint.md](docs/nikodym_bound_lean_blueprint.md)`,
`[docs/nikodym_construction_lean_blueprint.md](docs/nikodym_construction_lean_blueprint.md)`
and `[docs/algebra_backend_design.md](docs/algebra_backend_design.md)`; node-by-node
status is tracked in `[docs/PROGRESS.md](docs/PROGRESS.md)`.

The definition, in the style of the finite-field Kakeya definition of the
Formal Conjectures project, is

```lean
def Nikodym.IsNikodym {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (S : Finset (Fin n → F)) : Prop :=
  ∀ x, ∃ v, v ≠ 0 ∧ ∀ t : F, t ≠ 0 → x + t • v ∈ S
```

The target theorems, all in namespace `Nikodym`, are:

```lean
-- Lower bound, denominator-free integer form (blueprint node C10)
theorem card_compl_pow_mul_card_le (hd : 2 ≤ d) (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F ^ d - N.card) ^ 2 ^ (d - 1) * Fintype.card F ≤
      (8 * d ^ 2 + 1) ^ 2 ^ (d - 1) * Fintype.card F ^ (d * 2 ^ (d - 1))

-- Lower bound, displayed real form (blueprint node C11)
theorem card_ge_pow_sub (hd : 2 ≤ d) (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F : ℝ) ^ d -
        (8 * d ^ 2 + 1) * (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ))) ≤
      N.card

-- Upper bound (the construction)
theorem exists_isNikodym_card_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ (F : Type) [Field F] [Fintype F],
      (Fintype.card F).Prime → q₀ ≤ Fintype.card F →
        ∃ N : Finset (Fin d → F), IsNikodym N ∧
          (N.card : ℝ) ≤ (Fintype.card F : ℝ) ^ d -
            (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ)) - ε)
```



## Proof architecture (lower bound)

Following `docs/Nikodym_sharp_power_saving.tex` and the blueprint:

1. **Carrier theorem.** For an integral projective variety
  $A \subseteq \mathbb P^d_K$ of dimension $k$ and degree $\Delta$ containing
   $L$ affine $\mathbb F_q$-lines with private points,
   $L \le (8d^2+1)\Delta q^{k-2^{1-k}}$. The Nikodym bound is the case
   $A = \mathbb P^d$, $\Delta = 1$, with the witness lines of the complement.
2. **Two Hilbert-function estimates.** Normalized monotonicity
  $H(u)/\binom{u+d}{d} \le H(t)/\binom{t+d}{d}$ via standard monomials and a
   weighted shadow count, and the degree upper bound
   $H_A(t) \le \Delta\binom{t+k}{k}$ via linear Noether normalization and a
   norm-degree argument.
3. **Finite-grid interpolation.** Polynomials of degree
  $U = q(r-1) + d(q-1)$ interpolate arbitrary jets of order $< r$ at every
   grid point simultaneously; the local jet dimension is at least
   $\binom{r+k-1}{k}$.
4. **Interpolation cut.** Omitting the jet conditions at the $L$ private points
  yields a polynomial of degree $T = r(q-1)-1$, not vanishing on $A$, that
   vanishes on every selected line.
5. **Dimension induction.** The cut has components of dimension $k-1$ whose
  degrees sum to at most $T\Delta$; assigning lines to components and
   applying the inductive bound halves the saving at each step.

The blueprint carries this out in natural-number form,
$L^{2^{k-1}} q \le ((8d^2+1)\Delta)^{2^{k-1}} q^{k 2^{k-1}}$, and converts to
real exponents only in the final corollary.

## File guide


| File                                                                           | Contents                                                          |
| ------------------------------------------------------------------------------ | ----------------------------------------------------------------- |
| `[Nikodym/Definition.lean](Nikodym/Definition.lean)`                           | The `IsNikodym` predicate and elementary examples.                |
| `[Nikodym/Main.lean](Nikodym/Main.lean)`                                       | The three final theorems (fully proved).                          |
| `[FORMALIZATION.md](FORMALIZATION.md)`                                         | Correspondence between the mathematics and the Lean statements.   |
| `[docs/nikodym_bound_lean_blueprint.md](docs/nikodym_bound_lean_blueprint.md)` | Statement-level blueprint and dependency DAG for the lower bound. |
| `[docs/Nikodym_sharp_power_saving.tex](docs/Nikodym_sharp_power_saving.tex)`   | Source note for the lower bound.                                  |
| `[docs/nikodym_construction.tex](docs/nikodym_construction.tex)`               | Source note for the construction.                                 |




## Build

```sh
lake exe cache get  # download the precompiled Mathlib cache
lake build
```

The repository pins the Lean toolchain to `leanprover/lean4:v4.33.0-rc1` and
Mathlib to `v4.33.0-rc1`.

## Palomar submission surface

The repository follows the layout of the
[Palomar registry](https://palomar-registry.org/) starter template so that the
headline statements can be checked independently of the proof development:


| File                                                                     | Role                                                                                                                                                                                                            |
| ------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `[Challenge.lean](Challenge.lean)`                                       | Mathlib-only statement module: restates `IsNikodym` and the three theorems with `sorry`. This is the surface a reader should audit.                                                                             |
| `[Solution.lean](Solution.lean)`                                         | Imports `Nikodym.Main`, which proves the same declarations.                                                                                                                                                     |
| `[comparator.json](comparator.json)`                                     | Names the three compared theorems and the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`).                                                                                                       |
| `[formalization.yaml](formalization.yaml)`                               | Structured metadata: result description, sources, authorship, automation, review status, scope, and fidelity.                                                                                                   |
| `[scripts/verify-comparator.sh](scripts/verify-comparator.sh)`           | Runs the pinned [Comparator](https://github.com/leanprover/comparator), lean4export (`v4.33.0-rc1`), NanoDa and Landrun to check `Solution` against `Challenge` (Linux; used by the `Palomar checks` workflow). |
| `[scripts/check-submission-files.rb](scripts/check-submission-files.rb)` | Checks the files above against Palomar's mechanical requirements, including that `status.axioms` / `status.main_results` in `formalization.yaml` agree with `comparator.json`.                                 |
| `[scripts/check-metadata-schema.sh](scripts/check-metadata-schema.sh)`   | Validates `formalization.yaml` against the pinned upstream v0.4 JSON schema with `check-jsonschema`.                                                                                                            |
| `[scripts/check-axioms.rb](scripts/check-axioms.rb)`                     | Runs `#print axioms` on the compared theorems and requires the result to match `permitted_axioms` and the axiom lists in `formalization.yaml` (called at the end of `verify-comparator.sh`).                    |


Before submitting a commit, run the three metadata checks locally (the first two
need only Ruby and `pip install check-jsonschema`; the third builds the project):

```
ruby scripts/check-submission-files.rb
scripts/check-metadata-schema.sh
ruby scripts/check-axioms.rb
```

Submissions are made through [https://submit.palomar-registry.org/](https://submit.palomar-registry.org/)
with the full 40-character SHA of a pushed commit.