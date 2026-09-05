# Algebra backend design: discharging `AlgebraInterface`

Status: design only (no Lean written for the open nodes yet). Companion to
`docs/nikodym_bound_lean_blueprint.md` (nodes A02–A09, J01–J02, B01–B03) and
`Nikodym/LowerBound/Algebra/Interface.lean`.

Target: a term `algebraInterface (K : Type*) [Field K] (d : ℕ) : AlgebraInterface K d` for
**every** field `K`, i.e. proofs of the three fields (statements verbatim from `Interface.lean`):

```lean
hilbert_le_degree_mul_choose : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → ∀ t : ℕ,
  hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I)

choose_le_jetDim : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → ∀ x : Fin d → K,
  I ≤ pointIdeal x → ∀ r : ℕ, 1 ≤ r → (r + quotDim I - 1).choose (quotDim I) ≤ jetDim I x r

proper_cut : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → 2 ≤ quotDim I →
  ∀ (g : MvPolynomial (Fin d) K) (T : ℕ), g ∉ I → g.totalDegree ≤ T → I ⊔ Ideal.span {g} ≠ ⊤ →
  ∃ S : Finset (Ideal (MvPolynomial (Fin d) K)),
    (∀ J ∈ S, J.IsPrime) ∧ (∀ J ∈ S, I ⊔ Ideal.span {g} ≤ J) ∧
    (∀ J ∈ S, quotDim J + 1 = quotDim I) ∧ (∀ J ∈ S, 0 < degree J) ∧
    (∑ J ∈ S, degree J) ≤ T * degree I ∧
    (∀ Q : Ideal (MvPolynomial (Fin d) K), Q.IsPrime → I ⊔ Ideal.span {g} ≤ Q → ∃ J ∈ S, J ≤ Q)
```

Notation used below: `P := MvPolynomial (Fin d) K`, `P̂ := MvPolynomial (Fin (d+1)) K`
(index `0` is the homogenizing variable `X₀`, `Fin.succ i` is `Xᵢ`), `P_t := homogeneousSubmodule
(Fin d) K t`, `P_{≤t} := restrictTotalDegree (Fin d) K t`, `𝔪 := idealOfVars (Fin d) K = pointIdeal 0`,
`k := quotDim I`, `Δ := degree I`. Everything is over a field; "form" = homogeneous polynomial.

---

## 1. Global strategy

### 1.1 The three theorems are proved over infinite fields, then transported

Every algebraic input needs a **linear** Noether normalization (linear forms as parameters;
Mathlib's `exists_integral_inj_algHom_of_quotient` uses Nagata's nonlinear substitution and is
unusable for degree bookkeeping) and one **rational point** avoiding a nonzero polynomial. Both
need `Infinite K` (`Submodule.exists_forall_notMem_of_forall_ne_top`, `MvPolynomial.funext`).
Finite fields are handled by base change along `ι := MvPolynomial.map (algebraMap K K')` with
`K' := RatFunc K`, which is infinite (`Infinite.of_injective (algebraMap K[X] (RatFunc K))
(IsFractionRing.injective _ _)`).

Decision: **`RatFunc K`, not `AlgebraicClosure K`.** Reasons:

* `K ↪ RatFunc K` is *purely transcendental*; primes stay prime under `map ι`. Proof is two
  Mathlib steps: `MvPolynomial (Fin d) K[X] ≃ Polynomial P` (`optionEquivRight`/`finSuccEquiv`
  reindexing) with `Ideal.isPrime_map_C_of_isPrime`, then `IsLocalization.isPrime_of_isPrime_disjoint`
  with the instance `MvPolynomial.isLocalization` (needs `attribute [local instance]
  MvPolynomial.algebraMvPolynomial`). For an algebraic closure, primes need *not* stay prime
  (`X² + 1` over `ℝ`), so B03 would have to be re-derived through minimal primes of the extension,
  and inseparability appears in characteristic `p`.
* We only need `Infinite K'`; algebraic closedness buys nothing.
* Everything transported (`hilbert`, `quotDim`, `degree`, `jetDim`, `minimalPrimes`) is invariant
  under **any** field extension `K ⊆ K'` except primality; the transfer lemmas TR0–TR3, TR6 are
  written for arbitrary `[Algebra K K']`, only TR4/TR5 specialize to `RatFunc K`.

Alternative rejected: proving A02 over finite fields directly (Noether normalization with
higher-degree homogeneous parameters). It breaks the degree bookkeeping of A07/A08 and has no
Mathlib support.

Consequence for the file layout: the *core* theorems live in files that assume `[Infinite K]`;
`Nikodym/LowerBound/Algebra/BaseChange.lean` (new node **TR**) removes the hypothesis and builds
`algebraInterface`. The interface fields are proved directly over `K` from the infinite-field
cores plus TR (not by transporting the whole structure), because B03's finset must be
recognized as the finset of minimal primes.

### 1.2 Main simplifications relative to the blueprint

1. **A03 (Hilbert polynomial existence) is purely combinatorial.** By
   `hilbert_eq_sum_layerCard`, `hilbert I t` is the number of standard monomials of degree `≤ t`,
   a down-closed set of exponents. Slicing along the last variable and using the well-quasi-order
   on `Fin d → ℕ` (`Pi.wellQuasiOrderedLE`, `wellQuasiOrdered_le`) gives eventual polynomiality
   by induction on `d`. No graded modules, no Hilbert–Serre, works over every field, for every
   ideal.
2. **A06/A09 (generic freeness, graded chart) are replaced by a "conductor" argument.**
   For `R := P̂ ⧸ Iʰ` finite over `S := K[Y₀,…,Y_k]` we pick homogeneous `r₁,…,r_Δ ∈ R` forming a
   `Frac S`-basis of `Frac R`, put `M := span S {rᵢ}` (free) and choose `c ∈ S \ 0` with `c·R ⊆ M`.
   No localization, no `Module.FinitePresentation`, no `Algebra.norm_localization`, no
   dehomogenized chart ring. The fiber is taken at the *rational point* `(a₀, a) ∈ K^{k+1}` with
   `a₀ ≠ 0`, `c(a₀,a) ≠ 0`, in the hyperplane `Y₀ = a₀` (ideal `𝔮 := (Y₀ - a₀) + 𝔫^{t+1}`), whose
   quotient `S ⧸ 𝔮 ≅ K[y₁..y_k] ⧸ (y-a)^{t+1}` has dimension `(t+k).choose k`
   (`finrank_quotient_pointIdeal_pow`, already proved).
3. **A07 (norm degree) via scaling automorphisms**, not graded localizations: `σ_λ : Xᵢ ↦ λXᵢ`
   acts on `R`, `S`, their fraction fields; `Algebra.norm_eq_of_ringEquiv` gives
   `τ_λ(N F) = λ^{tΔ} N F` for `F ∈ R_t`; since `K` is infinite this forces `N F ∈ S_{tΔ}`.
4. **A04 (degree = generic rank) is a corollary** of the A08 upper bound and the lower bound
   `hilbert I t ≥ ∑ᵢ (t - eᵢ + k).choose k` from the free submodule `M`, plus one elementary
   lemma comparing leading coefficients of eventually-ordered polynomials.
5. **J01/J02 avoid associated graded rings and `dim gr = dim` entirely.** With the tangent-cone
   ideal `in(I)` (span of lowest-degree forms) and linear parameters `y₁..y_s` of `P ⧸ in(I)`
   (A02, no domain hypothesis), a single Nakayama step
   (`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) shows `𝔪` is minimal over
   `I + (y)`, so `k = height ≤ s` by `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`; the
   monomials `y^α`, `|α| < r`, are independent mod `I + 𝔪^r` by a lowest-degree-term argument.
6. **B02 uses only the affine→homogeneous direction of A05** (never "dehomogenization of a
   homogeneous prime is prime"): components `J ∈ minimalPrimes (I ⊔ (g))` are taken in `P`,
   homogenized to distinct primes `Jʰ ⊇ Iʰ + (gʰ)`, and the degree sum is bounded by
   inclusion–exclusion on graded pieces (`Submodule.finrank_sup_add_finrank_inf_eq`) plus the
   growth bound `homHilbert J' t = O(t^{dim-1})` from A02.

### 1.3 Helper notions (new definitions, all `noncomputable def`, no axioms)

| name | file | meaning |
|---|---|---|
| `homHilbert (J : Ideal P̂) (t : ℕ) : ℕ` | `Algebra/Homogenization.lean` | `finrank K ((homogeneousSubmodule (Fin (d+1)) K t).map (Ideal.Quotient.mkₐ K J).toLinearMap)` |
| `dehom : P̂ →ₐ[K] P` | same | `aeval (Fin.cases 1 X)` |
| `homogenizeTo (t : ℕ) (F : P) : P̂` | same | `∑ α ∈ F.support, monomial (Fin.cons (t - α.degree) α) (F.coeff α)` |
| `homogenization (I : Ideal P) : Ideal P̂` | same | `((I.comap dehom).homogeneousCore 𝒜).toIdeal` |
| `tangentIdeal (I : Ideal P) : Ideal P` | `Algebra/LocalParameters.lean` | `Ideal.span {F ∣ ∃ n, F.IsHomogeneous n ∧ F ∈ I ⊔ 𝔪 ^ (n+1)}` |
| `scaleEquiv (λ : Kˣ) : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K` | `Algebra/GradedNorm.lean` | `Xᵢ ↦ λ Xᵢ` |
| `evPoly (h : ℕ → ℕ) : Polynomial ℚ` | `Algebra/Interface.lean` (refactor) | the eventual polynomial of `h`; `affineHilbertPoly I = evPoly (hilbert I)` by `rfl` |

`evPoly` is the only touch to `Interface.lean`: it makes "same Hilbert function ⇒ same
`affineHilbertPoly`/`degree`" a one-liner across *different* fields (needed by TR2).

Convention: Mathlib's graded-ring instance on `MvPolynomial` is local; every file using
`Ideal.IsHomogeneous`/`homogeneousCore` must start with
`attribute [local instance] MvPolynomial.gradedAlgebra`.

---

## 2. Node specifications

Each node: Lean signature(s) (to be stated exactly like this, modulo naming polish), proof route
with Mathlib citations, difficulty (S ≈ ≤150 lines, M ≈ 150–400, L ≈ 400–800), dependencies.
All Mathlib names below were checked with `#check` against the pinned Mathlib.

### A01 (done) — `Algebra/Dimension.lean`

Used downstream: `ringKrullDim_eq_of_isIntegral`, `height_map_eq_ringKrullDim_of_isMaximal`,
`ringKrullDim_quotient_add_one_of_mem_minimalPrimes`,
`ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup`, `finite_minimalPrimes_sup`,
`quotDim_lt_of_lt`, `coe_quotDim`.

### D01 (new, small) — dimension of a quotient through its primes — `Algebra/DimensionExtra.lean`

```lean
theorem ringKrullDim_quotient_le_of_forall_isPrime {R : Type*} [CommRing R] (J : Ideal R) (n : ℕ)
    (h : ∀ p : Ideal R, p.IsPrime → J ≤ p → ringKrullDim (R ⧸ p) ≤ n) :
    ringKrullDim (R ⧸ J) ≤ n

theorem quotDim_sup_le_of_forall_lt {J : Ideal P} {n : ℕ}
    (h : ∀ p : Ideal P, p.IsPrime → J ≤ p → quotDim p ≤ n) (hJ : J ≠ ⊤) : quotDim J ≤ n
```

Route: a chain in `PrimeSpectrum (R ⧸ J)` starts at some `q₀`; let `p := q₀.comap`. Chains above
`q₀` correspond to chains in `PrimeSpectrum (R ⧸ p)` via `Ideal.map` along the surjection
`Ideal.Quotient.factor` (`Ideal.relIsoOfSurjective`, `Ideal.comap_map_of_surjective`), so its
length is `≤ ringKrullDim (R ⧸ p) ≤ n`. Use `Order.krullDim_le_of_strictMono` as in
`Dimension.lean`. **S–M.** Depends on: nothing new. Used by A02.d, B02.

### A02 — linear Noether normalization of a standard graded algebra — `Algebra/LinearNormalization.lean`

Stated for `n` variables (`Q := MvPolynomial (Fin n) K`, `𝔪ₙ := idealOfVars (Fin n) K`), over
`[Infinite K]`, for **any** homogeneous `J ≠ ⊤` (no domain hypothesis; J02 and B02 need the
non-domain case).

```lean
theorem exists_linear_normalization [Infinite K] (J : Ideal Q) (hJ : J ≠ ⊤)
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) :
    ∃ y : Fin (quotDim J) → Q,
      (∀ i, (y i).IsHomogeneous 1) ∧
      Function.Injective (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk J (y i)) :
        MvPolynomial (Fin (quotDim J)) K →ₐ[K] Q ⧸ J) ∧
      ∃ N : ℕ, 𝔪ₙ ^ N ≤ J ⊔ Ideal.span (Set.range y)

/-- graded Nakayama: the third conclusion gives module-finiteness and an explicit generating
set (classes of monomials of degree `< N`). -/
theorem finite_of_pow_idealOfVars_le {J : Ideal Q} (hJh : J.IsHomogeneous _) {s N : ℕ}
    {y : Fin s → Q} (hy : ∀ i, (y i).IsHomogeneous 1) (hN : 𝔪ₙ ^ N ≤ J ⊔ Ideal.span (Set.range y)) :
    letI := (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk J (y i))).toRingHom.toAlgebra
    Module.Finite (MvPolynomial (Fin s) K) (Q ⧸ J)
    -- plus the graded refinement: ∀ t ≥ N, P_t ≤ J ⊔ ∑ i, (y i) • P_{t-1}   (used by B02)
```

Route (sub-lemmas, each S):

* A02.a `exists_linear_form_notMem`: finitely many homogeneous primes `pᵢ` with `pᵢ ⊉ 𝔪ₙ`
  ⇒ ∃ linear form outside all of them. `Submodule.exists_forall_notMem_of_forall_ne_top` applied
  to the subspaces `pᵢ.comap (homogeneousSubmodule 1).subtype` of `P_1`, which are proper
  because a homogeneous ideal containing all `Xᵢ` contains `𝔪ₙ`.
* A02.b: a proper homogeneous ideal is `≤ 𝔪ₙ` (`mem_iff_homogeneousComponent_mem` in degree 0);
  a homogeneous prime is `= 𝔪ₙ` iff `quotDim = 0` iff it contains `P_1`.
* A02.c `IsHomogeneous.minimalPrimes`: minimal primes of a homogeneous ideal are homogeneous:
  for `q ∈ J.minimalPrimes`, `(q.homogeneousCore 𝒜).toIdeal` is prime
  (`Ideal.IsPrime.homogeneousCore`), contains `J` (`mem_homogeneousCore_of_homogeneous_of_mem` on
  homogeneous generators, `Ideal.IsHomogeneous.iff_exists`), and is `≤ q`
  (`toIdeal_homogeneousCore_le`), hence `= q` by minimality.
* A02.d `quotDim_sup_span_singleton_lt`: if `y ∈ P_1` avoids every minimal prime of `J`
  other than `𝔪ₙ` (finitely many: `Ideal.finite_minimalPrimes_of_isNoetherianRing`) and
  `quotDim J ≥ 1`, then `quotDim (J ⊔ span {y}) < quotDim J`. Every prime `q ⊇ J + (y)`
  contains a minimal prime `p` (`Ideal.exists_minimalPrimes_le`); either `p = 𝔪ₙ = q`
  (`quotDim = 0`) or `y ∉ p`, so `p < q` and `quotDim q < quotDim p ≤ quotDim J`
  (`quotDim_lt_of_lt`, `quotDim` antitone). Conclude with D01.
* A02.e: iterate `quotDim J` times ⇒ `y` with `quotDim (J ⊔ span (range y)) = 0`
  (all `J ⊔ span (range y)` remain homogeneous: `Ideal.IsHomogeneous.sup`, `homogeneous_span`).
* A02.f `pow_idealOfVars_le_of_quotDim_eq_zero`: homogeneous `J'`, `quotDim J' = 0`
  ⇒ `∃ N, 𝔪ₙ ^ N ≤ J'` (as implemented, no `J' ≠ ⊤` hypothesis; call as
  `pow_idealOfVars_le_of_quotDim_eq_zero hJh h0`). Its minimal primes are homogeneous (A02.c), proper, hence `≤ 𝔪ₙ`, and
  maximal (dimension 0 ⇒ `Ring.KrullDimLE 0` ⇒ `Ideal.IsPrime.isMaximal'`), hence `= 𝔪ₙ`; so
  `J'.radical = 𝔪ₙ` (`Ideal.sInf_minimalPrimes`) and `Ideal.exists_pow_le_of_le_radical_of_fg`.
* A02.g injectivity (`aeval_injective_of_pow_idealOfVars_le`, stated for any `s ≤ quotDim J`):
  with `S := MvPolynomial (Fin s) K`, finiteness (A02.h) gives
  `Algebra.IsIntegral S (Q ⧸ J)`; the image is `S ⧸ ker` and `ringKrullDim_eq_of_isIntegral` (A01,
  for the injective integral map `S ⧸ ker → Q ⧸ J`) gives `dim (S ⧸ ker) = s`; if `ker ≠ ⊥`,
  `ringKrullDim_quotient_succ_le_of_nonZeroDivisor` (domain `S`) gives `≤ s - 1`, contradiction.
* A02.h `finite_of_pow_idealOfVars_le`: induction on degree: a form of degree `t ≥ N` lies in
  `𝔪ₙ^N ≤ J + (y)`; taking its degree-`t` component (`homogeneousComponent_mem_of_mem`,
  component of `∑ yᵢ gᵢ` is `∑ yᵢ (gᵢ)_{t-1}`) puts it in `J + ∑ yᵢ P_{t-1}`. Hence `Q ⧸ J` is
  spanned over `S` by classes of monomials of degree `< N` (`Module.Finite.of_surjective` from a
  finite free module, or `Submodule.fg_def`).

Difficulty **L** (many small pieces; the algebra-instance plumbing via `RingHom.toAlgebra` as in
`Dimension.lean`). Depends on A01, D01. Splittable: (a,b,c,f) / (d,e) / (g,h) among three
people once the statement is fixed.

### A03 — eventual polynomiality of `hilbert` — `Algebra/HilbertPolynomial.lean`

```lean
/-- combinatorial core -/
theorem layerCard_eventually_polynomial {N : ℕ} (S : Set (Fin N → ℕ)) (hS : IsDownClosed S) :
    ∃ p : Polynomial ℚ, ∀ᶠ t : ℕ in atTop, (layerCard S t : ℚ) = p.eval (t : ℚ)

theorem hilbert_eventually_polynomial (I : Ideal P) :
    ∃ p : Polynomial ℚ, ∀ᶠ t : ℕ in atTop, (hilbert I t : ℚ) = p.eval (t : ℚ)

theorem hilbert_eventually_eq_affineHilbertPoly (I : Ideal P) :
    ∀ᶠ t : ℕ in atTop, (hilbert I t : ℚ) = (affineHilbertPoly I).eval (t : ℚ)
```

(`IsDownClosed` is whatever `StandardMonomials.lean` already uses for the standard-monomial set;
reuse its name.)

Route: induction on `N`. `N = 0`: `layerCard S t = 0` for `t ≥ 1`. Step: for `j : ℕ` the slice
`S_j := {a ∣ Fin.snoc a j ∈ S}` is down-closed and antitone in `j`; the chain stabilizes: if
`S_j ≠ S_{j+1}` infinitely often pick `x_j ∈ S_j \ S_{j+1}` and apply `wellQuasiOrdered_le` on
`Fin N → ℕ` (`Pi.wellQuasiOrderedLE`) to get `m < n` with `x_m ≤ x_n ∈ S_n ⊆ S_{m+1}`, so
`x_m ∈ S_{m+1}`, contradiction. With `S_j = S_J` for `j ≥ J`:
`layerCard S t = ∑_{j<J} layerCard S_j (t-j) + ∑_{u ≤ t-J} layerCard S_J u`. Eventually-polynomial
functions `ℕ → ℚ` are closed under finite sums, shifts and partial sums; for partial sums use
the basis `choosePoly 0, …, choosePoly n` of `degreeLT ℚ (n+1)` and Pascal
(`Nat.succ_add_choose`-type identity, `choosePoly_eval_natCast`). Finish with
`hilbert_eq_sum_layerCard`. **M.** Depends on: `Hilbert/StandardMonomials.lean`,
`Hilbert/Shadow.lean` only. Field-independent. **Ready now.**

### A05 — homogenization bridge — `Algebra/Homogenization.lean`

```lean
theorem dehom_homogenizeTo {t : ℕ} {F : P} (hF : F.totalDegree ≤ t) : dehom (homogenizeTo t F) = F
theorem isHomogeneous_homogenizeTo {t : ℕ} {F : P} (hF : F.totalDegree ≤ t) :
    (homogenizeTo t F).IsHomogeneous t
theorem homogenizeTo_dehom {t : ℕ} {G : P̂} (hG : G.IsHomogeneous t) : homogenizeTo t (dehom G) = G

theorem homogenization_isHomogeneous (I : Ideal P) : (homogenization I).IsHomogeneous _
theorem mem_homogenization_iff {t : ℕ} {G : P̂} (hG : G.IsHomogeneous t) (I : Ideal P) :
    G ∈ homogenization I ↔ dehom G ∈ I
theorem homogenizeTo_mem_homogenization_iff {t : ℕ} {F : P} (hF : F.totalDegree ≤ t) (I : Ideal P) :
    homogenizeTo t F ∈ homogenization I ↔ F ∈ I
theorem map_dehom_homogenization (I : Ideal P) : (homogenization I).map dehom = I
theorem homogenization_mono : Monotone (homogenization (K := K) (d := d))
theorem homogenization_injective : Function.Injective (homogenization (K := K) (d := d))
instance (I : Ideal P) [I.IsPrime] : (homogenization I).IsPrime
theorem X_zero_notMem_homogenization {I : Ideal P} (hI : I ≠ ⊤) : X 0 ∉ homogenization I
theorem homogenization_ne_top {I : Ideal P} (hI : I ≠ ⊤) : homogenization I ≠ ⊤

theorem homHilbert_homogenization (I : Ideal P) (t : ℕ) : homHilbert (homogenization I) t = hilbert I t

theorem ker_dehom : RingHom.ker dehom.toRingHom = Ideal.span {X 0 - 1}
theorem comap_dehom_eq (I : Ideal P) : I.comap dehom = homogenization I ⊔ Ideal.span {X 0 - 1}
theorem quotDim_homogenization (I : Ideal P) [I.IsPrime] : quotDim (homogenization I) = quotDim I + 1
```

Route:

* The monomial-level bijection between forms of degree `t` in `d+1` variables and polynomials of
  degree `≤ t` in `d` variables gives `dehom ∘ homogenizeTo t = id` on `P_{≤t}` and
  `homogenizeTo t ∘ dehom = id` on `P̂_t`. Hence `dehom` restricts to a `K`-linear isomorphism
  `P̂_t ≃ P_{≤t}` carrying `(homogenization I) ⊓ P̂_t` onto `I ⊓ P_{≤t}`
  (`mem_homogenization_iff`); rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) on both
  sides gives `homHilbert_homogenization`.
* `mem_homogenization_iff`: `⇐` is `Ideal.mem_homogeneousCore_of_homogeneous_of_mem`; `⇒` is
  `toIdeal_homogeneousCore_le`. Primality: `Ideal.IsPrime.homogeneousCore` applied to the prime
  `I.comap dehom` (`Ideal.IsPrime.comap`).
* `ker_dehom`: transport `Polynomial.ker_evalRingHom (1 : P)` along
  `MvPolynomial.finSuccEquiv K d` (`finSuccEquiv_X_zero`, `finSuccEquiv_X_succ`).
* `comap_dehom_eq`: `⊇` clear; for `G` with `dehom G ∈ I`, `G' := homogenizeTo N (dehom G)` lies
  in `homogenization I` and `dehom (G - G') = 0`.
* `quotDim_homogenization`: `P̂ ⧸ I.comap dehom ≃ P ⧸ I` (`Ideal.quotientKerAlgEquivOfSurjective`
  for `(Ideal.Quotient.mkₐ K I).comp dehom`, `dehom` surjective) has dimension `k`; in the domain
  `R := P̂ ⧸ homogenization I` the class of `X 0 - 1` is nonzero (a homogeneous ideal containing
  `X 0 - 1` contains `1`) and generates the prime `(I.comap dehom).map (mk _)`, the unique minimal
  prime over it (`Ideal.minimalPrimes_eq_subsingleton_self`); apply
  `ringKrullDim_quotient_add_one_of_mem_minimalPrimes` (A01) and `DoubleQuot.quotQuotEquivQuotOfLE`.

**M–L.** Depends on A01. Field-independent. **Ready now.**

### A06′ — homogeneous rational basis and conductor — `Algebra/FreeFiber.lean`

Setting (shared by A06′, A07′, A08, A04′): `[Infinite K]`, `I : Ideal P` prime, `k := quotDim I`,
`R := P̂ ⧸ homogenization I`, `y : Fin (k+1) → P̂` the linear forms from A02 for `homogenization I`
(so `quotDim = k+1` by A05), `S := MvPolynomial (Fin (k+1)) K`,
`g : S →ₐ[K] R := aeval (mk ∘ y)` (injective), `R` an `S`-algebra via `g.toRingHom.toAlgebra`,
`Module.Finite S R` (A02.h), `NoZeroSMulDivisors S R`, `FractionRing S`, `FractionRing R` with
`FractionRing.liftAlgebra` (needs `FaithfulSMul S R`, from injectivity).

```lean
/-- a homogeneous element of `R` of degree `e` is the class of a form of degree `e` -/
def IsHomogeneousElem' (r : R) (e : ℕ) : Prop := ∃ G : P̂, G.IsHomogeneous e ∧ Ideal.Quotient.mk _ G = r

theorem exists_homogeneous_fraction_basis :
    ∃ (Δ : ℕ) (r : Fin Δ → R) (e : Fin Δ → ℕ),
      (∀ i, IsHomogeneousElem' (r i) (e i)) ∧
      LinearIndependent S r ∧
      Nonempty (Module.Basis (Fin Δ) (FractionRing S) (FractionRing R)) -- with basis vectors algebraMap (r i)
      -- packaged: ∃ b : Basis (Fin Δ) (FractionRing S) (FractionRing R), ∀ i, b i = algebraMap R _ (r i)

theorem exists_conductor {Δ : ℕ} {r : Fin Δ → R} (hb : ...basis as above...) :
    ∃ c : S, c ≠ 0 ∧ ∀ x : R, c • x ∈ Submodule.span S (Set.range r)
```

Route: `R` is spanned over `S` by finitely many homogeneous classes (A02.h: monomials of degree
`< N`). Their images span a finite-dimensional `Frac S`-subalgebra `V ⊆ Frac R` containing the
image of `R`; `V` is a domain integral over the field `Frac S`, hence a field
(`Algebra.IsIntegral.isField_iff_isField`), hence contains every `algebraMap R _ x⁻¹`, hence
`V = ⊤` (`IsFractionRing.mk'_surjective`). Extract a basis from the spanning set with
`exists_linearIndependent`; `S`-independence follows from `Frac S`-independence by clearing
denominators (`IsLocalization.mk'_surjective`). Conductor: each of the finitely many `S`-generators
`gⱼ` of `R` is a `Frac S`-combination of the `rᵢ`; multiply denominators
(`IsLocalization.exist_integer_multiples`). **M.** Depends on A02, A05.

### A07′ — homogeneity of the norm — `Algebra/GradedNorm.lean`

```lean
def scaleEquiv (λ : Kˣ) : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K   -- Xᵢ ↦ λ Xᵢ
theorem scaleEquiv_apply_isHomogeneous {F} {t} (hF : F.IsHomogeneous t) (λ : Kˣ) :
    scaleEquiv λ F = C (λ ^ t : K) * F
theorem isHomogeneous_of_forall_scaleEquiv_eq [Infinite K] {F : MvPolynomial σ K} {e : ℕ}
    (h : ∀ λ : Kˣ, scaleEquiv λ F = C (λ ^ e : K) * F) : F.IsHomogeneous e

/-- with the setting of A06′: -/
theorem norm_mem_range_algebraMap (F : R) :
    ∃ s : S, algebraMap S (FractionRing S) s = Algebra.norm (FractionRing S) (algebraMap R (FractionRing R) F)
theorem norm_isHomogeneous {F : R} {t : ℕ} (hF : IsHomogeneousElem' F t) {s : S}
    (hs : algebraMap S _ s = Algebra.norm (FractionRing S) (algebraMap R _ F)) :
    s.IsHomogeneous (t * Module.finrank (FractionRing S) (FractionRing R))
```

Route: `norm_mem_range_algebraMap`: `F` is integral over `S` (`Module.Finite` ⇒
`Algebra.IsIntegral.of_finite`), so `Algebra.isIntegral_norm` (with `IsScalarTower S (Frac S)
(Frac R)`, provided by `FractionRing.isScalarTower_liftAlgebra`) makes the norm integral over `S`,
and `IsIntegrallyClosed.isIntegral_iff` (`MvPolynomial` over a field is a UFD, hence integrally
closed — instances exist) puts it in `S`. `norm_isHomogeneous`: `scaleEquiv λ` preserves
`homogenization I` (homogeneous ideal; `scaleEquiv_apply_isHomogeneous` componentwise), so it
induces `σ_λ : R ≃ₐ[K] R` (`Ideal.quotientEquivAlg`), and `σ_λ ∘ g = g ∘ τ_λ` where
`τ_λ := scaleEquiv λ` on `S` (check on `X i`: `MvPolynomial.algHom_ext`). Extend both to fraction
fields (`IsLocalization.ringEquivOfRingEquiv`), check compatibility with the algebra map by
`IsLocalization.ringHom_ext`, and apply `Algebra.norm_eq_of_ringEquiv`:
`τ̂_λ (N F) = N (σ̂_λ F) = N (λ^t F) = λ^{tΔ} N F` (`map_mul`, `Algebra.norm_algebraMap`,
`Module.finrank_eq_card_basis`). Then `isHomogeneous_of_forall_scaleEquiv_eq`: for a monomial `α`
of degree `j ≠ tΔ`, `(λ^j - λ^{tΔ}) · coeff α s = 0` for all `λ ∈ Kˣ`, so the polynomial
`(X^j - X^{tΔ}) · C (coeff α s) ∈ K[X]` has infinitely many roots and is zero
(`Polynomial.eq_zero_of_infinite_isRoot`). **M–L** (the fraction-field instance plumbing is the
risk; see §4). Depends on A06′ setting only (not on the basis).

Fallback if the fraction-field route is painful: work with the matrix `A` of multiplication by
`c²F` on `M` (basis `r`, homogeneous), show `τ_λ A = D_λ⁻¹ (λ^{2γ+t} A) D_λ` with
`D_λ = diag(λ^{eᵢ})` for **homogeneous** `c` of degree `γ` (choose `c` homogeneous: the
annihilator of the graded module `R ⧸ M` is homogeneous), take `det` (`Matrix.det_units_conj`),
and divide by `c^{2Δ}` with the lemma "a homogeneous multiple of a homogeneous element has a
homogeneous cofactor". This avoids `Frac` except for `norm_mem_range_algebraMap`.

### A08 — uniform Hilbert upper bound — `Hilbert/DegreeUpper.lean`

```lean
/-- core, with the generic rank in place of `degree` -/
theorem hilbert_le_rank_mul_choose [Infinite K] (I : Ideal P) [I.IsPrime] (t : ℕ) :
    hilbert I t ≤ Module.finrank (FractionRing S) (FractionRing R) * (t + quotDim I).choose (quotDim I)
    -- S, R as in A06′ (existentially packaged in the actual statement, see A04′)

theorem hilbert_le_degree_mul_choose_of_infinite [Infinite K] (I : Ideal P) [I.IsPrime] (t : ℕ) :
    hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I)
```

Route for the core (all in `R`, `S`; write `Δ := #basis`, `M := span S (range r)`,
`b : Basis (Fin Δ) S M := Module.Basis.span hr`):

1. Point: `c · Y₀ ≠ 0` in `S`, so by `MvPolynomial.funext` there is `p = (a₀, a) ∈ K^{k+1}` with
   `c p ≠ 0`, `a₀ ≠ 0`. Let `𝔫 := pointIdeal p ⊂ S` (maximal),
   `𝔮 := Ideal.span {Y₀ - C a₀} ⊔ 𝔫 ^ (t+1)`. Then `S ⧸ 𝔮 ≃ K[y₁..y_k] ⧸ pointIdeal a ^ (t+1)`
   (`finSuccEquiv` + `Polynomial.quotientSpanXSubCAlgEquiv`), so `finrank K (S ⧸ 𝔮) = (t+k).choose k`
   (`finrank_quotient_pointIdeal_pow`).
2. Map: `Φ : R_t →ₗ[K] (Fin Δ → S ⧸ 𝔮)`, `F ↦ fun i ↦ mk 𝔮 (b.repr ⟨c • F, _⟩ i)`, where
   `R_t := (homogeneousSubmodule _ _ t).map (mkₐ K (homogenization I))`, so
   `finrank K R_t = homHilbert (homogenization I) t = hilbert I t` (A05). Target has dimension
   `Δ · (t+k).choose k` (`Module.finrank_pi`). It remains to show `Φ` injective
   (`LinearMap.finrank_le_finrank_of_injective`).
3. Kernel: let `F ∈ R_t` with all coordinates `mᵢ` of `c F` in `𝔮`. For each `j`,
   `c² F rⱼ = ∑ᵢ mᵢ (c rᵢ rⱼ)` with `c rᵢ rⱼ ∈ M`, so the matrix `A` of multiplication by `c² F`
   on `M` (w.r.t. `b`) has entries in `𝔮` and `A.det ∈ 𝔮 ^ Δ` (`Matrix.det_apply`, products of
   `Δ` elements of `𝔮`).
4. Norm: `algebraMap (A.det) = Algebra.norm (Frac S) (c² F) = c^{2Δ} · N F`
   (`Algebra.norm_eq_matrix_det` w.r.t. the `Frac S`-basis `algebraMap ∘ r`; coordinates commute
   with `algebraMap` by uniqueness `Basis.repr`; `Algebra.norm_algebraMap`). With
   `N F = algebraMap s` (A07′), `c^{2Δ} s ∈ 𝔮^Δ`. `𝔮^Δ` is `𝔫`-primary
   (`Ideal.isPrimary_of_isMaximal_radical`: `𝔫^{t+1} ≤ 𝔮 ≤ 𝔫`) and `c ∉ 𝔫`, so `s ∈ 𝔮^Δ ≤
   span {Y₀ - C a₀} ⊔ 𝔫^{Δ(t+1)}` (binomial expansion of `(A ⊔ B)^Δ`).
5. Order vs degree: `s` is a form of degree `tΔ < Δ(t+1)` (A07′). Apply `ev : S →ₐ[K] K[y]`,
   `Y₀ ↦ a₀`: `ev s ∈ (pointIdeal a)^{Δ(t+1)}` has total degree `≤ tΔ`, so `ev s = 0`
   (translate to the origin, `mem_pow_idealOfVars_iff`). Hence `s (a₀, ·) ≡ 0`; by homogeneity
   `s (λa₀, λ·) = λ^{tΔ} s(a₀, ·) = 0` for all `λ ≠ 0`, so `Y₀ · s` vanishes on `K^{k+1}` and
   `s = 0` (`MvPolynomial.funext`). Thus `A.det = 0`.
6. `A.det = 0` ⇒ `c² F` kills a nonzero `m ∈ M` (`Matrix.exists_mulVec_eq_zero_iff` over the domain
   `S`), so `F = 0` in the domain `R`. Hence `Φ` is injective.

**L.** Depends on A02, A05, A06′, A07′; step 1 needs `Jets/Defs.lean`. Then A08 final =
core + A04′ (`degree I = Δ`).

### A04′ — `degree = generic rank`, `natDegree = quotDim` — `Algebra/Degree.lean`

```lean
/-- lower bound from the free submodule -/
theorem sum_choose_le_hilbert [Infinite K] (I : Ideal P) [I.IsPrime] :
    ∃ (Δ : ℕ) (e : Fin Δ → ℕ), 0 < Δ ∧ ∀ t, (∑ i, (t - e i + quotDim I).choose (quotDim I)) ≤ hilbert I t
    -- (with the same Δ as in the core upper bound; package both bounds in one ∃)

theorem natDegree_affineHilbertPoly [Infinite K] (I : Ideal P) [I.IsPrime] :
    (affineHilbertPoly I).natDegree = quotDim I
theorem leadingCoeff_affineHilbertPoly [Infinite K] (I : Ideal P) [I.IsPrime] :
    (affineHilbertPoly I).leadingCoeff = (degree I : ℚ) / (quotDim I).factorial
theorem degree_pos [Infinite K] (I : Ideal P) [I.IsPrime] : 0 < degree I

/-- elementary polynomial lemmas (field-free, put in `Algebra/PolyAsymptotics.lean`) -/
theorem Polynomial.coeff_le_coeff_of_eventually_le {p q : Polynomial ℚ} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ᶠ t : ℕ in atTop, p.eval (t : ℚ) ≤ q.eval (t : ℚ)) : p.coeff n ≤ q.coeff n
theorem Polynomial.natDegree_le_of_eventually_between {p q₁ q₂ : Polynomial ℚ} {n : ℕ}
    (h₁ : q₁.natDegree ≤ n) (h₂ : q₂.natDegree ≤ n)
    (h : ∀ᶠ t : ℕ in atTop, q₁.eval (t : ℚ) ≤ p.eval (t : ℚ) ∧ p.eval (t : ℚ) ≤ q₂.eval (t : ℚ)) :
    p.natDegree ≤ n
theorem Polynomial.coeff_sub_comp_X_sub_C {p : Polynomial ℚ} {n : ℕ} (hp : p.natDegree ≤ n + 1) (e : ℚ) :
    (p - p.comp (X - C e)).coeff n = (n + 1) * e * p.coeff (n + 1)
```

Route: lower bound: `(sᵢ) ↦ ∑ sᵢ rᵢ` maps `⊕ᵢ S_{t - eᵢ}` injectively (`LinearIndependent S r`)
into `R_t` (`rᵢ` homogeneous of degree `eᵢ`), and `finrank K S_j = (j + k).choose k`. Polynomial
lemmas: `q - p ≥ 0` eventually and `natDegree ≤ n` ⇒ `coeff n ≥ 0`, else
`Polynomial.tendsto_atBot_of_leadingCoeff_nonpos` along `Nat.cast` (`tendsto_natCast_atTop_atTop`).
Then `p := affineHilbertPoly I` (exists by A03) is eventually between
`∑ᵢ choosePoly k ∘ (X - eᵢ)` and `Δ · choosePoly k`, both of degree `k` with `coeff k = Δ / k!`
(`natDegree_choosePoly`, `leadingCoeff_choosePoly`), so `natDegree p ≤ k`, `coeff k p = Δ/k!`,
hence `natDegree p = k`, `degree I = ⌊Δ⌋₊ = Δ`. **M.** Depends on A03, A08-core.

### J01 — tangent cone and local parameters — `Algebra/LocalParameters.lean`

```lean
theorem tangentIdeal_isHomogeneous (I : Ideal P) : (tangentIdeal I).IsHomogeneous _
theorem mem_tangentIdeal_iff {n : ℕ} {F : P} (hF : F.IsHomogeneous n) (I : Ideal P) :
    F ∈ tangentIdeal I ↔ F ∈ I ⊔ 𝔪 ^ (n + 1)
theorem tangentIdeal_ne_top {I : Ideal P} (hI : I ≤ 𝔪) : tangentIdeal I ≠ ⊤

/-- the parameters of the tangent cone bound the height of `𝔪 / I` -/
theorem quotDim_le_of_pow_idealOfVars_le_tangentIdeal_sup [Infinite K] (I : Ideal P) [I.IsPrime]
    (hI : I ≤ 𝔪) {s N : ℕ} {y : Fin s → P} (hy : ∀ i, (y i).IsHomogeneous 1)
    (hN : 𝔪 ^ N ≤ tangentIdeal I ⊔ Ideal.span (Set.range y)) : quotDim I ≤ s
```

Route: `mem_tangentIdeal_iff` `⇒`: `F = ∑ aⱼ Fⱼ` with `Fⱼ ∈ I ⊔ 𝔪^{nⱼ+1}` homogeneous of degree
`nⱼ`; the degree-`n` component is `∑ (aⱼ)_{n-nⱼ} Fⱼ ∈ I ⊔ 𝔪^{n+1}` (forms times
`I ⊔ 𝔪^{nⱼ+1}` land in `I ⊔ 𝔪^{n+1}`). Height bound: from `hN` and `mem_tangentIdeal_iff`,
`𝔪^N ≤ J₀ ⊔ 𝔪^{N+1}` with `J₀ := I ⊔ span (range y)` (components of degree `n ≥ N` of an element
of `𝔪^N`, `mem_pow_idealOfVars_iff`). So the `P`-submodule `Nₘ := (𝔪^N ⊔ J₀).map (mkQ J₀)` of
`P ⧸ J₀` satisfies `Nₘ ≤ 𝔪 • Nₘ` and is f.g.; `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`
gives `ρ` with `ρ - 1 ∈ 𝔪`, `ρ 𝔪^N ≤ J₀`. Any prime `J₀ ≤ q ≤ 𝔪` has `ρ ∉ q` (else `1 ∈ 𝔪`), so
`𝔪^N ≤ q`, `q = 𝔪`: `𝔪 ∈ J₀.minimalPrimes`. Push to `P ⧸ I`
(`Ideal.minimalPrimes_map_of_surjective`): `𝔪.map (mk I) ∈ (span (mk I '' range y)).minimalPrimes`,
so `height ≤ s` (`Ideal.height_le_card_of_mem_minimalPrimes_span_finset`, `Finset.card_image_le`)
and `height (𝔪.map (mk I)) = quotDim I` (`height_map_eq_ringKrullDim_of_isMaximal`, `coe_quotDim`).
**M.** Depends on A01; `[Infinite K]` only enters through the caller. Field-independent
lemma, **ready now** (A02 is used only in J02).

### J02 — local jet minimum — `Jets/LowerBound.lean`

```lean
theorem choose_le_jetDim_origin [Infinite K] (I : Ideal P) [I.IsPrime] (hI : I ≤ 𝔪) {r : ℕ} (hr : 1 ≤ r) :
    (r + quotDim I - 1).choose (quotDim I) ≤ jetDim I 0 r
theorem choose_le_jetDim_of_infinite [Infinite K] (I : Ideal P) [I.IsPrime] (x : Fin d → K)
    (hx : I ≤ pointIdeal x) {r : ℕ} (hr : 1 ≤ r) :
    (r + quotDim I - 1).choose (quotDim I) ≤ jetDim I x r
```

Route: A02 on `J := tangentIdeal I` gives `s`, `y`, `N`, injectivity of `aeval y` into
`P ⧸ tangentIdeal I`, and `𝔪^N ≤ J ⊔ span (range y)`; J01 gives `k ≤ s`. Claim: the classes of
`aeval y (monomial α 1)`, `α : Fin s →₀ ℕ`, `α.degree < r`, are `K`-linearly independent in
`P ⧸ (I ⊔ 𝔪^r)`. If `∑ c_α y^α ∈ I ⊔ 𝔪^r`, let `n < r` be the least degree with some `c_α ≠ 0`
and `Fₙ := ∑_{|α|=n} c_α y^α ≠ 0` (injectivity of `aeval y` into `P ⧸ J`, applied to a nonzero
form of degree `n` in `s` variables, gives `Fₙ ∉ J`, in particular `Fₙ ≠ 0`); then
`Fₙ ∈ I ⊔ 𝔪^{n+1}` (subtract the higher terms, which lie in `𝔪^{n+1}`, and use `n + 1 ≤ r`),
so `Fₙ ∈ J` by `mem_tangentIdeal_iff` — contradiction. Hence
`jetDim I 0 r ≥ #{α : Fin s →₀ ℕ ∣ degree α < r} = (r - 1 + s).choose s ≥ (r - 1 + k).choose k`
(`card_exponentsLE`, `Nat.choose_symm_add`, `Nat.choose_le_choose`). General `x`: `translate x`
(`jetSpaceEquivOrigin`, `pointIdeal_eq_map`, `Ideal.map_isPrime_of_equiv`, `quotDim` invariant
under `Ideal.map` of a ring equivalence). **M.** Depends on A02, J01.

### B01 — hypersurface section — `Algebra/HypersurfaceDegree.lean`

```lean
theorem homHilbert_sup_span_singleton_add {Q : Ideal P̂} [Q.IsPrime] (hQ : Q.IsHomogeneous _)
    {G : P̂} {e : ℕ} (hG : G.IsHomogeneous e) (hGQ : G ∉ Q) {t : ℕ} (ht : e ≤ t) :
    homHilbert (Q ⊔ Ideal.span {G}) t + homHilbert Q (t - e) = homHilbert Q t
theorem homHilbert_anti {A B : Ideal P̂} (h : A ≤ B) (t : ℕ) : homHilbert B t ≤ homHilbert A t
```

Route: multiplication by `G` maps `P̂_{t-e} ⧸ Q_{t-e}` injectively (prime, `G ∉ Q`) into
`P̂_t ⧸ Q_t` with image `((Q ⊔ (G)) ⊓ P̂_t) ⧸ Q_t` (degree-`t` components of `q + G u`:
`homogeneousComponent_mem_of_mem`); rank–nullity. **S–M.** Field-independent, **ready now**
(after `homHilbert` is defined in A05; the definition can be split off first).

### B02 — degree sum over components — `Algebra/ComponentDegree.lean`

```lean
theorem homHilbert_inf_add_homHilbert_sup {A B : Ideal P̂} (hA : A.IsHomogeneous _) (hB : B.IsHomogeneous _) (t : ℕ) :
    homHilbert (A ⊓ B) t + homHilbert (A ⊔ B) t = homHilbert A t + homHilbert B t

/-- growth bound from A02 -/
theorem homHilbert_le_mul_choose [Infinite K] {J : Ideal P̂} (hJ : J ≠ ⊤) (hJh : J.IsHomogeneous _)
    {m : ℕ} (hm : quotDim J ≤ m + 1) :
    ∃ C : ℕ, ∀ t, homHilbert J t ≤ C * (t + m).choose m

/-- main statement, purely in terms of `homHilbert` and eventual polynomials -/
theorem sum_coeff_le_of_components [Infinite K] {n : ℕ} (hn : 1 ≤ n)
    {Q₀ : Ideal P̂} [Q₀.IsPrime] (hQ₀ : Q₀.IsHomogeneous _) (hdim₀ : quotDim Q₀ = n + 2)
    {G : P̂} {e : ℕ} (hG : G.IsHomogeneous e) (hGQ : G ∉ Q₀)
    (𝒬 : Finset (Ideal P̂)) (h𝒬 : ∀ Q ∈ 𝒬, Q.IsPrime ∧ Q.IsHomogeneous _ ∧ quotDim Q = n + 1 ∧ Q₀ ⊔ Ideal.span {G} ≤ Q)
    {p₀ : Polynomial ℚ} (hp₀ : ∀ᶠ t : ℕ in atTop, (homHilbert Q₀ t : ℚ) = p₀.eval t) (hd₀ : p₀.natDegree ≤ n + 1)
    {p : Ideal P̂ → Polynomial ℚ} (hp : ∀ Q ∈ 𝒬, ∀ᶠ t : ℕ in atTop, (homHilbert Q t : ℚ) = (p Q).eval t)
    (hd : ∀ Q ∈ 𝒬, (p Q).natDegree ≤ n) :
    ∑ Q ∈ 𝒬, (p Q).coeff n ≤ e * (n + 1) * p₀.coeff (n + 1)
```

Route: (i) inf/sup identity is `Submodule.finrank_sup_add_finrank_inf_eq` on `A_t, B_t` (graded
pieces of homogeneous ideals: `(A ⊓ B)_t = A_t ⊓ B_t`, `(A ⊔ B)_t = A_t ⊔ B_t`). (ii) growth: A02
gives `s := quotDim J` linear forms with `𝔪̂^N ≤ J ⊔ (y)`; by A02.h every form of degree `t ≥ N`
is in `J ⊔ ∑ yᵢ P̂_{t-1}`, so `homHilbert J t ≤ ∑_{u<N} homHilbert J u · #{α : Fin s →₀ ℕ ∣ |α| = t-u}
≤ C · (t + s - 1).choose (s - 1) ≤ C · (t+m).choose m`. (iii) Induction over `𝒬` (ordered
arbitrarily): `∑_Q homHilbert Q t = homHilbert (⨅ 𝒬) t + ∑ᵢ homHilbert (Qᵢ ⊔ ⨅_{j<i} Qⱼ) t`.
Each correction ideal has `quotDim ≤ n`: a prime containing it contains `Qᵢ` and some `Qⱼ`
(`Ideal.IsPrime.inf_le'`), `Qⱼ ≠ Qᵢ` with equal `quotDim` forces `Qᵢ < q` (`quotDim_lt_of_lt`),
so `quotDim q ≤ n`; conclude with D01 and bound by (ii) with `m = n - 1`. (iv)
`homHilbert (⨅ 𝒬) t ≤ homHilbert (Q₀ ⊔ (G)) t = p₀(t) - p₀(t-e)` (B01, `homHilbert_anti`).
(v) `Polynomial.coeff_le_coeff_of_eventually_le` with `n`, using
`Polynomial.coeff_sub_comp_X_sub_C` for the right-hand side and that the correction polynomial
`C · choosePoly (n-1)` has degree `n - 1 < n`. **L.** Depends on A02, B01, D01, A04′'s
polynomial lemmas.

### B03 — affine proper cut — `Algebra/ProperCut.lean`

```lean
theorem proper_cut_of_infinite [Infinite K] (I : Ideal P) [I.IsPrime] (hk : 2 ≤ quotDim I)
    (g : P) (T : ℕ) (hg : g ∉ I) (hT : g.totalDegree ≤ T) (hne : I ⊔ Ideal.span {g} ≠ ⊤) :
    (∀ J ∈ (I ⊔ Ideal.span {g}).minimalPrimes, 0 < degree J) ∧
    ∑ J ∈ (finite_minimalPrimes_sup I g).toFinset, degree J ≤ T * degree I
```

Route: `S := minimalPrimes` as a finset. For `J ∈ S`: prime, `quotDim J + 1 = k`
(`ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup`, A01), `0 < degree J` (A04′).
Homogenize: `Qⱼ := homogenization J` is a homogeneous prime with `quotDim = k` (A05), contains
`Q₀ ⊔ (G)` where `Q₀ := homogenization I` (`quotDim = k+1`), `G := homogenizeTo (totalDegree g) g`
(`homogenizeTo_mem_homogenization_iff`, `homogenization_mono`), `G ∉ Q₀`, `e = totalDegree g ≥ 1`
(else `I ⊔ (g) = ⊤`). `J ↦ Qⱼ` is injective (`homogenization_injective`), so `∑_J degree J = ∑_Q …`
(`Finset.sum_image`). Feed B02 with `n := k - 1`, `p₀ := affineHilbertPoly I`,
`p Q := affineHilbertPoly (Q.map dehom)` (`homHilbert_homogenization`,
`hilbert_eventually_eq_affineHilbertPoly`, `natDegree_affineHilbertPoly`); B02 yields
`∑ degree J / (k-1)! ≤ e · k · degree I / k!`, i.e. `∑ degree J ≤ e · degree I ≤ T · degree I`.
**M.** Depends on A01, A03, A04′, A05, B02.

### TR — base change `K → K'` — `Algebra/BaseChange.lean`

`ι := MvPolynomial.map (algebraMap K K') : P →+* P'`, `P' := MvPolynomial (Fin d) K'`,
`[Algebra K K']` arbitrary unless stated.

```lean
/-- TR0: coefficient extraction along a `K`-linear functional -/
def coeffProj (π : K' →ₗ[K] K) : P' →ₗ[K] P   -- coefficientwise π
theorem coeffProj_map (hπ : π 1 = 1) (f : P) : coeffProj π (ι f) = f
theorem coeffProj_map_mul (f : P) (g' : P') : coeffProj π (ι f * g') = f * coeffProj π g'
theorem coeffProj_mem_of_mem_map (I : Ideal P) {g' : P'} (hg' : g' ∈ I.map ι) : coeffProj π g' ∈ I
theorem totalDegree_coeffProj_le (g' : P') : (coeffProj π g').totalDegree ≤ g'.totalDegree
theorem sum_smul_map_coeffProj (b : Module.Basis β K K') (g' : P') :   -- finite sum over b.repr support
    g' = ∑ j ∈ (…), (b j) • ι (coeffProj (b.coord j) g')

/-- TR1 -/
theorem comap_map_eq_self (I : Ideal P) : (I.map ι).comap ι = I
theorem map_ne_top_iff (I : Ideal P) : I.map ι ≠ ⊤ ↔ I ≠ ⊤
theorem map_le_map_iff (I J : Ideal P) : I.map ι ≤ J.map ι ↔ I ≤ J
theorem map_injective : Function.Injective (Ideal.map ι : Ideal P → Ideal P')
theorem mem_map_iff (I : Ideal P) (f : P) : ι f ∈ I.map ι ↔ f ∈ I
theorem totalDegree_map (f : P) : (ι f).totalDegree = f.totalDegree   -- support_map_of_injective

/-- TR2 -/
theorem hilbert_map (I : Ideal P) (t : ℕ) : hilbert (I.map ι) t = hilbert I t
theorem affineHilbertPoly_map (I : Ideal P) : affineHilbertPoly (I.map ι) = affineHilbertPoly I
theorem degree_map (I : Ideal P) : degree (I.map ι) = degree I

/-- TR3 -/
theorem quotDim_map (I : Ideal P) : quotDim (I.map ι) = quotDim I

/-- TR4 (K' = RatFunc K) -/
theorem isPrime_map_ratFunc (I : Ideal P) [I.IsPrime] : (I.map (MvPolynomial.map (algebraMap K (RatFunc K)))).IsPrime

/-- TR5 (K' = RatFunc K) -/
theorem minimalPrimes_map_ratFunc (I : Ideal P) : (I.map ι).minimalPrimes = Ideal.map ι '' I.minimalPrimes

/-- TR6 -/
theorem jetIdeal_map (I : Ideal P) (x : Fin d → K) (r : ℕ) :
    (jetIdeal I x r).map ι = jetIdeal (I.map ι) (fun i ↦ algebraMap K K' (x i)) r
theorem jetDim_eq_hilbert (I : Ideal P) (x : Fin d → K) {r : ℕ} (hr : 1 ≤ r) :
    jetDim I x r = hilbert (jetIdeal I x r) (r - 1)
theorem jetDim_map (I : Ideal P) (x : Fin d → K) (r : ℕ) (hr : 1 ≤ r) :
    jetDim (I.map ι) (fun i ↦ algebraMap K K' (x i)) r = jetDim I x r

/-- TR7 -/
instance : Infinite (RatFunc K)
theorem algebraInterface (K : Type*) [Field K] (d : ℕ) : AlgebraInterface K d
```

Routes: TR0 via `MvPolynomial.coeff_map`, `coeff_mul`, and `Ideal.map = span (ι '' I)` with
`Submodule.span_induction`. TR1: `f = coeffProj π (ι f) ∈ I` for `ι f ∈ I.map ι`, with `π 1 = 1`
(extend `{1}` to a basis: `Module.Basis.extend`, or any dual functional). TR2: for
`V := I ⊓ P_{≤t}` with `K`-basis `vᵢ`, the `ι vᵢ` form a `K'`-basis of `I.map ι ⊓ P'_{≤t}`
(spanning by `sum_smul_map_coeffProj` + `coeffProj_mem_of_mem_map` + `totalDegree_coeffProj_le`;
independence by applying `coeffProj (b.coord j)` and `Basis.ext_elem`); rank–nullity on both
sides. Then `affineHilbertPoly_map` is `congrArg evPoly (funext hilbert_map)`. TR3: Noether
normalization `g : MvPolynomial (Fin s) K →ₐ[K] P ⧸ I` (Mathlib, nonlinear is fine here) base
changes to `g'` into `P' ⧸ I.map ι`, still integral (map the monic witnesses through
`Polynomial.map`; integral elements form a subalgebra containing the generators) and injective
(TR0), so both dimensions equal `s` by `ringKrullDim_eq_of_isIntegral`. TR4: as in §1.1. TR5:
`⊇`: `J.map ι` is prime (TR4), contains `I.map ι`, and is minimal because a prime `q` between
them contracts to `J` (TR1, `Ideal.comap_mono`) so `q ⊇ (q.comap ι).map ι = J.map ι`
(`Ideal.map_comap_le`). `⊆`: `q ∈ (I.map ι).minimalPrimes` contains some `J.map ι` with
`J ∈ I.minimalPrimes` (apply `Ideal.exists_minimalPrimes_le` to `q.comap ι ⊇ I`), hence equals it.
TR6: `Ideal.map_sup`, `Ideal.map_pow`, `pointIdeal_eq_span`, `Ideal.map_span`;
`jetDim_eq_hilbert` from `map_restrictTotalDegree_eq_top_of_pow_idealOfVars_le` transported by
`translate` and `finrank_top`. TR7: assemble the three fields from
`hilbert_le_degree_mul_choose_of_infinite`, `choose_le_jetDim_of_infinite`,
`proper_cut_of_infinite` over `RatFunc K`; for B03 take
`S := (finite_minimalPrimes_sup I g).toFinset` and use TR5 + `Finset.sum_image` + `degree_map`;
the dimension and covering clauses come from A01/Mathlib directly over `K`.

Difficulty: TR0–TR2 **M**, TR3 **M**, TR4–TR5 **M**, TR6–TR7 **S**. Depends on the cores only
for TR7; TR0–TR6 are **ready now** and field-generic.

---

## 3. Dependency DAG and schedule

```
                A01 (done)          Hilbert/StandardMonomials (done)      Jets/Defs (done)
                 │    │                       │                                 │
        ┌────────┘    └──────┐               A03                               │
        ▼                    ▼                │                                 │
       D01                  A05 ──────────────┼──────────┐                      │
        │                    │                │          │                      │
        ▼                    │                │          ▼                      │
       A02 ◄─────────────────┘                │         B01                     │
      ╱ │ ╲                                   │          │                      │
     ╱  │  ╲                                  │          │                      │
   J01  │   A06′ ──► A07′                     │          │                      │
    │   │      ╲       │                      │          │                      │
    ▼   │       ▼      ▼                      │          │                      │
   J02  │      A08-core ◄─────────────────────┘          │                      │
        │          │                                     │                      │
        │          ▼                                     │                      │
        │        A04′ (+ PolyAsymptotics) ──────► B02 ◄──┘                      │
        │          │                               │                            │
        ▼          ▼                               ▼                            │
     A08-final   (degree_pos)                    B03                            │
        │                                          │                            │
        └──────────────┬───────────────────────────┘                            │
                       ▼                                                        │
                    TR7 = algebraInterface  ◄──── TR0–TR6 (independent) ◄───────┘
```

Parallel work packages (each independently mergeable; interfaces are the signatures in §2):

| wave | packages (parallel) | prerequisites |
|---|---|---|
| 0 (now) | **A03** (combinatorics) · **A05** (homogenization, incl. `homHilbert`) · **D01** · **J01** · **TR0–TR2** · **TR4–TR5** · **TR3** · **TR6** · **PolyAsymptotics** (the three `Polynomial` lemmas) · `evPoly` refactor | none beyond done nodes |
| 1 | **A02** (three sub-packages a–c–f / d–e / g–h) · **B01** | D01, `homHilbert` |
| 2 | **J02** · **A06′** · **B02-(i),(ii),(iii)** (inf/sup identity, growth bound, correction-dimension lemma) | A02, A05 |
| 3 | **A07′** · **A08-core** · **B02-(iv),(v)** | A06′, B01 |
| 4 | **A04′** · **B03** | A08-core, A03, B02 |
| 5 | **A08-final**, **TR7** | everything |

Critical path: D01 → A02 → A06′ → A07′ → A08-core → A04′ → A08-final → TR7 (≈ 6 sequential
L/M nodes). A02 is the bottleneck; start it first and split it three ways. J02 and B03 hang off
A02 with short tails and can absorb spare people.

---

## 4. Mathlib coverage, risks, fallbacks

Verified present (names `#check`ed): `Submodule.exists_forall_notMem_of_forall_ne_top`,
`MvPolynomial.funext`, `Ideal.IsPrime.homogeneousCore`, `Ideal.IsHomogeneous.radical`,
`Ideal.homogeneous_span`, `Ideal.IsHomogeneous.iff_exists/iff_eq`, `mem_homogeneousCore_of_homogeneous_of_mem`,
`toIdeal_homogeneousCore_le`, `MvPolynomial.mem_iff_homogeneousComponent_mem`,
`homogeneousComponent_mem_of_mem`, `Ideal.exists_pow_le_of_le_radical_of_fg`, `Ideal.sInf_minimalPrimes`,
`Ideal.height_le_card_of_mem_minimalPrimes_span_finset`, `Ideal.minimalPrimes_map_of_surjective`,
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`, `Ideal.IsPrime.inf_le'`,
`Submodule.finrank_sup_add_finrank_inf_eq`, `Module.finrank_pi`, `Module.Basis.span`,
`exists_linearIndependent`, `Algebra.norm_eq_matrix_det`, `Algebra.norm_algebraMap`,
`Algebra.norm_eq_of_ringEquiv`, `Algebra.isIntegral_norm`, `IsIntegrallyClosed.isIntegral_iff`,
`FractionRing.liftAlgebra`, `Algebra.IsIntegral.isField_iff_isField`, `Matrix.exists_mulVec_eq_zero_iff`,
`Ideal.isPrimary_iff`/`isPrimary_of_isMaximal_radical`, `Polynomial.ker_evalRingHom`,
`Polynomial.quotientSpanXSubCAlgEquiv`, `Polynomial.eq_zero_of_infinite_isRoot`,
`Polynomial.tendsto_atBot_of_leadingCoeff_nonpos`, `wellQuasiOrdered_le`, `Pi.wellQuasiOrderedLE`,
`Ideal.isPrime_map_C_of_isPrime`, `MvPolynomial.isLocalization`, `IsLocalization.isPrime_of_isPrime_disjoint`,
`MvPolynomial.support_map_of_injective`, `mem_pow_idealOfVars_iff`, `exists_integral_inj_algHom_of_quotient`,
`Order.krullDim_le_of_strictMono`, `Ideal.relIsoOfSurjective`, `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`.

Not in Mathlib (we build them; all elementary):

| gap | node | fallback |
|---|---|---|
| linear/graded Noether normalization | A02 | none needed; the prime-avoidance construction above is standard. Risk: `RingHom.toAlgebra` instance juggling — copy the pattern from `Dimension.lean`. |
| minimal primes of a homogeneous ideal are homogeneous | A02.c | 10 lines from `Ideal.IsPrime.homogeneousCore`. |
| graded Nakayama / finiteness from `𝔪^N ≤ J + (y)` | A02.h | degree induction; no module-graded API needed. |
| `homogenization`, `dehom`, degree-`t` bijection | A05 | explicit monomial maps; `Finsupp` bookkeeping only. |
| Hilbert polynomial existence | A03 | WQO route above; **no** need for `Polynomial.hilbertPoly`/Hilbert–Serre (whose `eq_hilbertPoly_of_forall_coeff_eq_eval` needs `CharZero` and power series). |
| norm of a homogeneous element is homogeneous | A07′ | scaling automorphisms (primary) or matrix conjugation (fallback, §2 A07′). |
| generic freeness | — | eliminated by the conductor argument; if someone prefers it, `Module.FinitePresentation.exists_free_localizedModule_powers` + `Algebra.norm_localization` exist but bring `IsLocalization` plumbing. |
| dimension ≤ Hilbert growth | B02.(ii) | from A02.h directly, no `Ring.KrullDimLE`/module dimension theory. |
| leading-coefficient comparison | PolyAsymptotics | 3 lemmas, ~100 lines, `Polynomial.tendsto_*` + `tendsto_natCast_atTop_atTop`. |
| primes stay prime under `K → RatFunc K` | TR4 | if the `MvPolynomial.isLocalization` instance path is awkward, reprove via `Ideal.isPrime_map_C_of_isPrime` iterated through `optionEquivRight` and then `IsLocalization.isPrime_of_isPrime_disjoint` on `Polynomial P → P'`. |

Principal risks and mitigations:

1. **Fraction-field instance plumbing in A07′/A08** (`FractionRing.liftAlgebra`, `IsScalarTower`,
   `Algebra.norm` w.r.t. `Basis` built from `algebraMap ∘ r`). Mitigation: isolate everything
   that mentions `FractionRing` in one file (`GradedNorm.lean`) behind the two theorems
   `norm_mem_range_algebraMap`, `norm_isHomogeneous` and the identity
   `algebraMap S _ (A.det) = c^{2Δ} · N F`; A08 never touches `FractionRing` otherwise. If it
   stalls, use the matrix-conjugation fallback for homogeneity (only integrality then needs
   `Frac`).
2. **A02 instance management** (algebra structures from `aeval y`). Mitigation: state A02's
   output as raw data (`Function.Injective (aeval …)`, `𝔪^N ≤ …`) and let consumers install
   `RingHom.toAlgebra` locally, exactly as `Dimension.lean` does.
3. **Homogeneous-component arithmetic** (components of products, of elements of `J ⊔ (y)`).
   Provide once in `Algebra/GradedLemmas.lean` (wave 0, S): `homogeneousComponent (m+n) (F * G) =
   F * homogeneousComponent n G` for `F` homogeneous of degree `m`, components of finite sums,
   `(A ⊔ B)_t = A_t ⊔ B_t`, `(A ⊓ B)_t = A_t ⊓ B_t` for homogeneous ideals.
4. **`quotDim` conventions**: `quotDim ⊤ = 0` junk. All A02 statements carry `J ≠ ⊤`; B02's
   correction ideals may be `⊤` (then `homHilbert = 0`, fine) — handle by `by_cases`.
5. **Finset-of-minimal-primes API**: `finite_minimalPrimes_sup` gives a `Set.Finite`; TR5 must
   be stated at the `Set` level and converted with `Set.Finite.toFinset` + `Finset.image`.

---

## 5. Immediately assignable (no blockers)

* **A03** `Algebra/HilbertPolynomial.lean` — combinatorial, self-contained.
* **A05** `Algebra/Homogenization.lean` — start with `homHilbert`, `dehom`, `homogenizeTo`, the
  degree-`t` bijection and `homHilbert_homogenization`; `quotDim_homogenization` last.
* **D01** `Algebra/DimensionExtra.lean` and **GradedLemmas** `Algebra/GradedLemmas.lean`.
* **J01** `Algebra/LocalParameters.lean` (tangent ideal + Nakayama/height bound).
* **B01** `Algebra/HypersurfaceDegree.lean` (needs only the `homHilbert` definition; take it from
  A05's first commit or define it locally and reconcile).
* **PolyAsymptotics** `Algebra/PolyAsymptotics.lean` (three lemmas) and the `evPoly` refactor
  of `Interface.lean` (keep `affineHilbertPoly I = evPoly (hilbert I)` definitional).
* **TR0–TR2**, **TR3**, **TR4–TR5**, **TR6** `Algebra/BaseChange.lean` — four independent
  sub-packages.
* **A02** can also start now against the fixed signature, with D01 stubbed as a `sorry`-free
  dependency once it lands (D01 is small; do it first in the same PR if needed).

Everything else (A06′, A07′, A08, A04′, J02, B02, B03, TR7) is unblocked as soon as A02 and A05
merge.
