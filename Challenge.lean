/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# The sharp finite-field Nikodym exponent: advertised statements

This is the small, self-contained statement surface for the
[Palomar](https://palomar-registry.org/) submission.  It imports only Mathlib, restates the
single definition needed (`Nikodym.IsNikodym`, identical to `Nikodym/Definition.lean`), and
states the three headline theorems of the project with deliberate `sorry` holes.  The proved
versions, with exactly the same names and types, are supplied by `Solution.lean`, which imports
the full development in `Nikodym/`.

## The problem

Let `F` be a finite field with `q` elements and `d ≥ 2`.  A set `N ⊆ F^d` is a *Nikodym set*
if through every point `x ∈ F^d` there is a line `x + F • v` (with `v ≠ 0`) all of whose points
other than `x` lie in `N`.  Write `Nik(d, q)` for the minimum size of a Nikodym set in `F_q^d`.
Before this work the best general lower bound was the Kakeya-derived
`Nik(d, q) ≥ q^d / 2^{d-1} + O(q^{d-1})`, and it was open whether `Nik(d, q) = (1 - o(1)) q^d`;
the question addressed here is the sharp *power saving* `q^d - Nik(d, q)` (see the README for
the comparison with prior work).

## The results

* **Lower bound** (`card_compl_pow_mul_card_le`, `card_ge_pow_sub`): for every finite field `F`
  with `q` elements, every `d ≥ 2`, and every Nikodym set `N ⊆ F^d`,
  `|N| ≥ q^d - (8 d^2 + 1) · q^{d - 2^{1-d}}`.
  The first theorem is the equivalent denominator-free integer form obtained by raising both
  sides to the power `2^{d-1}`:
  `(q^d - |N|)^{2^{d-1}} · q ≤ (8 d^2 + 1)^{2^{d-1}} · q^{d · 2^{d-1}}`;
  the second is the displayed real inequality.  No restriction on the characteristic is made.

* **Upper bound** (`exists_isNikodym_card_le`): for every `d ≥ 2` and `ε > 0`, every finite field
  `F` of sufficiently large *prime* cardinality `q` contains a Nikodym set `N ⊆ F^d` with
  `|N| ≤ q^d - q^{d - 2^{1-d} - ε}`.

Together these show that the exponent `d - 2^{1-d}` of the power saving is sharp along primes.

## Conventions

* `Fintype.card F` is the field size `q`; `F^d` is modelled as `Fin d → F`.
* In `card_compl_pow_mul_card_le`, `Fintype.card F ^ d - N.card` is natural-number subtraction;
  since `N ⊆ F^d` it is never truncated, and the statement is an inequality in `ℕ`.
* In the real statements, `(x : ℝ) ^ (y : ℝ)` is Mathlib's real power `Real.rpow` and `2 ^ (1 - d)`
  is computed in `ℝ` (so `2 ^ (1 - (d : ℝ)) = 2^{1-d}` is a genuine reciprocal for `d ≥ 2`).
* The upper bound is stated only for prime `q`; the lower bound holds for every prime power `q`.
-/

namespace Nikodym

/--
A set `S ⊆ 𝔽_qⁿ` is a Nikodym set if for every point `x ∈ 𝔽_qⁿ` there is a line through `x`
all of whose points other than `x` lie in `S`. Lines are parametrised as `x + t • v` with
`v ≠ 0`, so the condition reads `x + t • v ∈ S` for all `t ≠ 0`.
-/
def IsNikodym {F : Type*} [Field F] [Fintype F] {n : ℕ} (S : Finset (Fin n → F)) : Prop :=
  ∀ x, ∃ v, v ≠ 0 ∧ ∀ t : F, t ≠ 0 → x + t • v ∈ S

variable {F : Type*} [Field F] [Fintype F] {d : ℕ}

/-- **Lower bound, integer form.**  Every Nikodym set `N ⊆ F^d`, `d ≥ 2`, satisfies
`(q^d - |N|)^{2^{d-1}} · q ≤ (8 d^2 + 1)^{2^{d-1}} · q^{d · 2^{d-1}}`, where `q = |F|`.
This is the denominator-free form of `|N| ≥ q^d - (8 d^2 + 1) · q^{d - 2^{1-d}}`. -/
theorem card_compl_pow_mul_card_le (hd : 2 ≤ d) (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F ^ d - N.card) ^ 2 ^ (d - 1) * Fintype.card F ≤
      (8 * d ^ 2 + 1) ^ 2 ^ (d - 1) * Fintype.card F ^ (d * 2 ^ (d - 1)) := by
  sorry

/-- **Lower bound, real form.**  Every Nikodym set `N ⊆ F^d`, `d ≥ 2`, satisfies
`|N| ≥ q^d - (8 d^2 + 1) · q^{d - 2^{1-d}}`, where `q = |F|` and the powers are real powers. -/
theorem card_ge_pow_sub (hd : 2 ≤ d) (N : Finset (Fin d → F)) (hN : IsNikodym N) :
    (Fintype.card F : ℝ) ^ d -
        (8 * d ^ 2 + 1) * (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ))) ≤
      N.card := by
  sorry

/-- **Upper bound.**  For `d ≥ 2` and `ε > 0`, there is a threshold `q₀` such that every finite
field `F` of prime cardinality `q ≥ q₀` contains a Nikodym set `N ⊆ F^d` with
`|N| ≤ q^d - q^{d - 2^{1-d} - ε}`. -/
theorem exists_isNikodym_card_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ (F : Type) [Field F] [Fintype F],
      (Fintype.card F).Prime → q₀ ≤ Fintype.card F →
        ∃ N : Finset (Fin d → F), IsNikodym N ∧
          (N.card : ℝ) ≤ (Fintype.card F : ℝ) ^ d -
            (Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ)) - ε) := by
  sorry

end Nikodym
