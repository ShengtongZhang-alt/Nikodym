/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Dimension theory of finitely generated domains over a field

Blueprint node A01.
-/

namespace Nikodym.LowerBound

open Ideal

section IntegralExtension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Blueprint A01 (1): `comap` along an integral extension is strictly monotone on primes. -/
theorem primeSpectrum_comap_strictMono_of_isIntegral [Algebra.IsIntegral R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hPQ ⊢
  exact Ideal.IsIntegral.comap_lt_comap hPQ

/-- Blueprint A01 (1): the Krull dimension does not go up along an integral extension. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono _ primeSpectrum_comap_strictMono_of_isIntegral

/-- Blueprint A01 (1), going up along chains: a strict chain of primes in `R` lifts to a strict
chain of the same length in an integral extension `S` (with injective structure map), whose last
element lies over the last element of the original chain. -/
theorem exists_ltSeries_length_eq_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, hQ, hQx⟩ := (Ideal.nonempty_primesOver (S := S) x.asIdeal).some
    refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, by simp, ?_⟩
    ext1
    simpa [PrimeSpectrum.comap_asIdeal] using hQx.over.symm
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hlt : l.last.asIdeal < x.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hx
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      rw [← PrimeSpectrum.comap_asIdeal, hlast]
      exact hlt.le
    obtain ⟨Q, hLQ, hQ, hQx⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal L.last.asIdeal hle
    have hLQ' : L.last < ⟨Q, hQ⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine lt_of_le_of_ne hLQ fun h ↦ hlt.ne ?_
      have h' := congrArg (Ideal.comap (algebraMap R S)) h
      rwa [← PrimeSpectrum.comap_asIdeal, hlast, hQx] at h'
    refine ⟨L.snoc ⟨Q, hQ⟩ hLQ', by simp [hlen], ?_⟩
    ext1
    simpa [PrimeSpectrum.comap_asIdeal] using hQx

/-- Blueprint A01 (1): the Krull dimension does not go down along an integral extension with
injective structure map (lying over + going up). -/
theorem ringKrullDim_ge_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  obtain ⟨L, hL, -⟩ := exists_ltSeries_length_eq_of_isIntegral (S := S) l
  exact le_iSup_of_le L (by rw [hL])

/-- Blueprint A01 (1): **integral extensions preserve Krull dimension.** -/
theorem ringKrullDim_eq_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral ringKrullDim_ge_of_isIntegral

end IntegralExtension

section MvPolynomial

variable (K : Type*) [Field K]

/-- Blueprint A01 (2): the polynomial ring in `s` variables over a field has dimension `s`. -/
theorem ringKrullDim_mvPolynomial_fin (s : ℕ) : ringKrullDim (MvPolynomial (Fin s) K) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- Blueprint A01 (3): **maximal ideals of a polynomial ring over a field have full height.** -/
theorem height_eq_of_isMaximal_mvPolynomial_fin :
    ∀ (s : ℕ) (𝔫 : Ideal (MvPolynomial (Fin s) K)), 𝔫.IsMaximal → 𝔫.height = s
  | 0, 𝔫, h => by
    haveI := h
    let e := (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv
    have hmax : (𝔫.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rcases Ideal.eq_bot_or_top (𝔫.map e) with h0 | h0
    · rw [← e.height_map 𝔫, h0, Ideal.height_bot]
      simp
    · exact absurd h0 hmax.ne_top
  | s + 1, 𝔫, h => by
    haveI := h
    let e := (MvPolynomial.finSuccEquiv K s).toRingEquiv
    haveI : (𝔫.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hmax : ((𝔫.map e).under (MvPolynomial (Fin s) K)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing (𝔫.map e)
    haveI := Ideal.over_under (A := MvPolynomial (Fin s) K) (𝔫.map e)
    rw [← e.height_map 𝔫, Polynomial.height_eq_height_add_one ((𝔫.map e).under _) (𝔫.map e),
      height_eq_of_isMaximal_mvPolynomial_fin s _ hmax]
    push_cast
    rfl

end MvPolynomial

section AffineDomain

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- Blueprint A01 (2): **Noether normalization gives the dimension.** There is an injective
`K`-algebra map from a polynomial ring in `s` variables into `A`, over which `A` is integral, and
`s` is the Krull dimension of `A`. -/
theorem exists_mvPolynomial_algHom_injective_isIntegral :
    ∃ (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A), Function.Injective g ∧
      (g : MvPolynomial (Fin s) K →+* A).IsIntegral ∧ ringKrullDim A = s := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  refine ⟨s, g, hinj, hint, ?_⟩
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  rw [ringKrullDim_eq_of_isIntegral (R := MvPolynomial (Fin s) K), ringKrullDim_mvPolynomial_fin]

/-- Blueprint A01 (2): the Krull dimension of a finitely generated domain over a field is a natural
number. -/
theorem exists_ringKrullDim_eq_natCast (K) [Field K] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨s, -, -, -, hs⟩ := exists_mvPolynomial_algHom_injective_isIntegral (K := K) (A := A)
  exact ⟨s, hs⟩

/-- Blueprint A01 (2): a finitely generated domain over a field has finite Krull dimension. -/
theorem finiteRingKrullDim (K) [Field K] [Algebra K A] [Algebra.FiniteType K A] :
    FiniteRingKrullDim A := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast (A := A) K
  rw [finiteRingKrullDim_iff_ne_bot_and_top, hn, ← WithBot.coe_natCast, ← WithBot.coe_top]
  exact ⟨WithBot.coe_ne_bot, fun h ↦ ENat.coe_ne_top n (WithBot.coe_inj.mp h)⟩

section Normalized

/-! In this section `A` carries a fixed Noether normalization: an integral, injective algebra
structure over the polynomial ring `MvPolynomial (Fin s) K`. -/

variable {s : ℕ} [Algebra (MvPolynomial (Fin s) K) A]
  [Algebra.IsIntegral (MvPolynomial (Fin s) K) A] [FaithfulSMul (MvPolynomial (Fin s) K) A]
  [IsNoetherianRing A]

/-- Blueprint A01 (4), auxiliary: the extension of a maximal ideal of the polynomial ring to `A`
lies over it. -/
private theorem map_liesOver_of_isMaximal (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ((𝔪.under (MvPolynomial (Fin s) K)).map (algebraMap (MvPolynomial (Fin s) K) A)).LiesOver
      (𝔪.under (MvPolynomial (Fin s) K)) :=
  ⟨le_antisymm Ideal.le_comap_map (Ideal.comap_mono (Ideal.map_le_iff_le_comap.mpr le_rfl))⟩

/-- Blueprint A01 (4), auxiliary: over a fixed Noether normalization in `s` variables, every
maximal ideal of `A` has height `s`. -/
private theorem height_eq_of_isMaximal_aux (𝔪 : Ideal A) [𝔪.IsMaximal] : 𝔪.height = s := by
  set S := MvPolynomial (Fin s) K
  set 𝔫 := 𝔪.under S with h𝔫
  haveI : 𝔫.IsMaximal := Ideal.IsMaximal.under S 𝔪
  haveI := Ideal.over_under (A := S) 𝔪
  haveI : (𝔫.map (algebraMap S A)).LiesOver 𝔫 := map_liesOver_of_isMaximal 𝔪
  have hfib : (𝔪.map (Ideal.Quotient.mk (𝔫.map (algebraMap S A)))).height = 0 := by
    have hdim : ringKrullDim (A ⧸ 𝔫.map (algebraMap S A)) ≤ 0 := by
      calc ringKrullDim (A ⧸ 𝔫.map (algebraMap S A))
          ≤ ringKrullDim (S ⧸ 𝔫) := ringKrullDim_le_of_isIntegral
        _ = 0 := ringKrullDim_eq_zero_of_isField
            ((Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔫).mp inferInstance)
    have h := (Ideal.height_le_ringKrullDim_of_isPrime
      (I := 𝔪.map (Ideal.Quotient.mk (𝔫.map (algebraMap S A))))).trans hdim
    rw [← WithBot.coe_zero, WithBot.coe_le_coe] at h
    exact nonpos_iff_eq_zero.mp h
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔫 𝔪, hfib, add_zero,
    height_eq_of_isMaximal_mvPolynomial_fin K s 𝔫 inferInstance]

/-- Blueprint A01 (5), auxiliary: over a fixed Noether normalization in `s` variables, a prime of
height one in `A` has quotient of dimension `s - 1`. -/
private theorem ringKrullDim_quotient_add_one_aux (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ringKrullDim (A ⧸ P) + 1 = s := by
  set S := MvPolynomial (Fin s) K
  set Q := P.under S with hQ
  haveI := Ideal.over_under (A := S) P
  have hQbot : Q ≠ ⊥ := Ideal.under_ne_bot S (Ideal.ne_bot_of_height_eq_one hP)
  have hQ1 : Q.height = 1 := by
    apply le_antisymm
    · have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown Q P
      rw [hP] at h
      exact h ▸ le_self_add
    · exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr
        (by rwa [Ne, Ideal.height_eq_zero_iff_eq_bot]))
  obtain ⟨p, hpQ, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (inferInstance : Q.IsPrime) hQbot
  have hQp : Q = Ideal.span {p} := Ideal.eq_span_singleton_of_height_eq_one hQ1 hpQ hp
  have h1 : ringKrullDim (A ⧸ P) = ringKrullDim (S ⧸ Q) := ringKrullDim_eq_of_isIntegral
  have h2 : ringKrullDim (S ⧸ Q) + 1 ≤ s := by
    rw [hQp, ← ringKrullDim_mvPolynomial_fin K s]
    exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hp.ne_zero)
  have h3 : (s : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Q) + 1 := by
    obtain ⟨𝔫, h𝔫, hQ𝔫⟩ := Q.exists_le_maximal Ideal.IsPrime.ne_top'
    haveI := h𝔫
    have h := Ideal.height_le_ringKrullDim_quotient_add_one (p := 𝔫) (r := p) (hQ𝔫 hpQ)
    rwa [height_eq_of_isMaximal_mvPolynomial_fin K s 𝔫 h𝔫, WithBot.coe_natCast, ← hQp] at h
  rw [h1]
  exact le_antisymm h2 h3

end Normalized

/-- Blueprint A01 (4): **maximal ideals of an affine domain have height equal to the
dimension.** -/
theorem height_eq_ringKrullDim_of_isMaximal (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    (𝔪.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint, hs⟩ :=
    exists_mvPolynomial_algHom_injective_isIntegral (K := K) (A := A)
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  haveI := h𝔪
  rw [height_eq_of_isMaximal_aux (K := K) 𝔪, hs]
  exact WithBot.coe_natCast s

/-- Blueprint A01 (4): `ℕ∞`-valued form of `height_eq_ringKrullDim_of_isMaximal`. -/
theorem height_eq_of_isMaximal_of_ringKrullDim_eq {n : ℕ} (hn : ringKrullDim A = n)
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) : 𝔪.height = n := by
  have h := height_eq_ringKrullDim_of_isMaximal (K := K) 𝔪 h𝔪
  rw [hn, ← WithBot.coe_natCast] at h
  exact WithBot.coe_inj.mp h

/-- Blueprint A01 (5): **a minimal prime over a nonzero element drops the dimension by exactly
one.** -/
theorem ringKrullDim_quotient_add_one_of_mem_minimalPrimes {f : A} (hf : f ≠ 0) {P : Ideal A}
    (hP : P ∈ (Ideal.span {f}).minimalPrimes) :
    ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint, hs⟩ :=
    exists_mvPolynomial_algHom_injective_isIntegral (K := K) (A := A)
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  haveI : P.IsPrime := hP.1.1
  have hfP : f ∈ P := hP.1.2 (Ideal.mem_span_singleton_self f)
  have hPbot : P ≠ ⊥ := fun h ↦ hf ((Submodule.mem_bot A).mp (h ▸ hfP))
  have hP1 : P.height = 1 := by
    haveI : (Ideal.span {f}).IsPrincipal := ⟨⟨f, rfl⟩⟩
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
    exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr
      (by rwa [Ne, Ideal.height_eq_zero_iff_eq_bot]))
  rw [hs]
  exact ringKrullDim_quotient_add_one_aux (K := K) P hP1

end AffineDomain

end Nikodym.LowerBound
