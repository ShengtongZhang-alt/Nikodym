# Formalization notes

## Target statements

The final theorems are declared in `Nikodym/Main.lean` and are fully proved:
the axiom report of each of them (`#print axioms`) contains only `propext`,
`Classical.choice` and `Quot.sound`.

- `Nikodym.card_compl_pow_mul_card_le` — the lower bound in natural-number
  form, blueprint node C10.
- `Nikodym.card_ge_pow_sub` — the lower bound as displayed in
  `docs/Nikodym_sharp_power_saving.tex`, Corollary 2 (label `cor:nikodym`),
  blueprint node C11.
- `Nikodym.exists_isNikodym_card_le` — the construction,
  `docs/nikodym_construction.tex`, Corollary 1.2 (label `cor:uniform`).

The same three statements, together with the definition `Nikodym.IsNikodym`,
are restated verbatim in the Mathlib-only module `Challenge.lean` for the
Palomar registry; `comparator.json` lists them, and Comparator checks that
`Solution.lean` (which imports `Nikodym.Main`) proves exactly those statements
from the standard axioms.

## Correspondence with the papers

- **Ambient space.** $\mathbb F_q^d$ is `Fin d → F` for a finite field `F`
  with `Fintype.card F = q`. The lower bound is stated for every finite field,
  matching "every prime power $q$" in the source note. The construction is
  stated for fields of prime cardinality, matching "all sufficiently large
  primes $q$".
- **Nikodym sets.** `IsNikodym S` says: for every `x` there is `v ≠ 0` such
  that `x + t • v ∈ S` for all `t ≠ 0`. This is exactly
  $\ell \setminus \{x\} \subseteq S$ for the line $\ell = x + \mathbb F_q v$.
  A Nikodym set is a `Finset (Fin d → F)`, so its cardinality is `S.card`.
  The definition follows the `IsKakeyaFinite` convention of the Formal
  Conjectures project.
- **The complement.** $|\mathbb F_q^d \setminus N|$ is written
  `Fintype.card F ^ d - N.card` in `ℕ`; since `N.card ≤ Fintype.card F ^ d`
  this natural subtraction is the true difference.
- **Integer form of the lower bound.** With $C = 8d^2+1$ and $m = 2^{d-1}$,
  the inequality $|B|^m q \le C^m q^{dm}$ is equivalent to
  $|B| \le C q^{d - 1/m} = C q^{d - 2^{1-d}}$ after taking $m$-th roots. The
  integer form is the one produced by the induction in the blueprint; the real
  form is a presentation corollary and the only place where `Real.rpow` is
  used.
- **Real powers.** `(Fintype.card F : ℝ) ^ ((d : ℝ) - 2 ^ (1 - (d : ℝ)))` is
  `Real.rpow` with a real exponent; `2 ^ (1 - (d : ℝ))` is likewise `rpow`
  since `1 - d` is negative.
- **Construction.** The statement quantifies over a threshold `q₀` first and
  then over all finite fields `F` of prime cardinality at least `q₀`, which is
  the meaning of "for all sufficiently large primes $q$". The set produced is
  the complement of the product set $P$ in the construction; only its
  existence and cardinality are asserted.

## Hypotheses that are deliberately absent

- No assumption that $q$ is prime in the lower bound.
- No restriction on the characteristic.
- No compactness, measurability, or dimension-theoretic notions: everything is
  finite combinatorics at the interface.

## Toolchain

The repository pins Lean to `leanprover/lean4:v4.33.0-rc1` in
`lean-toolchain` and Mathlib to `v4.33.0-rc1` in `lakefile.toml`.
