# The Sharp Finite-Field Nikodym Exponent in Lean

**Authors:** Shengtong Zhang and collaborators

This repository is a Lean 4 and Mathlib formalization project for the sharp
power saving in the finite-field Nikodym problem: the lower bound proved by
finite-grid interpolation, and the matching construction.

**Status: complete.** Both the lower bound and the construction are proved in
full: the three final theorems in [`Nikodym/Main.lean`](Nikodym/Main.lean)
build without `sorry`, and `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound` for each of them. The formalization plans
are in [`docs/nikodym_bound_lean_blueprint.md`](docs/nikodym_bound_lean_blueprint.md),
[`docs/nikodym_construction_lean_blueprint.md`](docs/nikodym_construction_lean_blueprint.md)
and [`docs/algebra_backend_design.md`](docs/algebra_backend_design.md); node-by-node
status is tracked in [`docs/PROGRESS.md`](docs/PROGRESS.md).

## The theorem

Let $q$ be a prime power and $d \ge 2$. A set $N \subseteq \mathbb F_q^d$ is a
*Nikodym set* if for every $x \in \mathbb F_q^d$ there is an affine line $\ell$
through $x$ with $\ell \setminus \{x\} \subseteq N$.

**Lower bound.** For every Nikodym set $N \subseteq \mathbb F_q^d$,

$$
|N| \ge q^d - (8d^2+1)\, q^{\,d - 2^{1-d}}.
$$

**Upper bound.** For every $\varepsilon > 0$ and all sufficiently large primes
$q$, there is a Nikodym set $N \subseteq \mathbb F_q^d$ with

$$
|N| \le q^d - q^{\,d - 2^{1-d} - \varepsilon}.
$$

Together these give $\operatorname{Nik}(d,q) = q^d - q^{\,d-2^{1-d}+o(1)}$.

## Lean statements

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
   $L \le (8d^2+1)\,\Delta\, q^{\,k-2^{1-k}}$. The Nikodym bound is the case
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

| File                                                     | Contents                                                        |
| -------------------------------------------------------- | --------------------------------------------------------------- |
| [`Nikodym/Definition.lean`](Nikodym/Definition.lean)     | The `IsNikodym` predicate and elementary examples.              |
| [`Nikodym/Main.lean`](Nikodym/Main.lean)                 | The three final theorems (fully proved).                        |
| [`FORMALIZATION.md`](FORMALIZATION.md)                   | Correspondence between the mathematics and the Lean statements. |
| [`docs/nikodym_bound_lean_blueprint.md`](docs/nikodym_bound_lean_blueprint.md) | Statement-level blueprint and dependency DAG for the lower bound. |
| [`docs/Nikodym_sharp_power_saving.tex`](docs/Nikodym_sharp_power_saving.tex)   | Source note for the lower bound.                              |
| [`docs/nikodym_construction.tex`](docs/nikodym_construction.tex)               | Source note for the construction.                             |

## Build

```sh
lake exe cache get  # download the precompiled Mathlib cache
lake build
```

The repository pins the Lean toolchain to `leanprover/lean4:v4.33.0-rc1` and
Mathlib to `v4.33.0-rc1`.
