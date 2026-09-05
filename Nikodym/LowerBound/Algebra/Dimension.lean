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

end AffineDomain

end Nikodym.LowerBound
