/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Nikodym.Construction.Scaffold

/-!
# Fibers: the trace fiber

This file implements blueprint node C01 of `docs/nikodym_construction_lean_blueprint.md`.

* C01: `Scaffold.exists_trace_fiber`: under `Scaffold` with `K₀ > 0`, for every real `T ≥ 1` there
  is an integer `s` and a `Finset` `A ⊆ boxFinset T` on which the trace is constantly `s`, with
  `(T / (n * K₀)) ^ n / ((2 * n + 1) * T) ≤ #A`.

Throughout, `n` denotes `Fintype.card ι`.
-/

namespace Nikodym

namespace Scaffold

section TraceFiber

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}

/-- Blueprint C01: the trace of an element of the box of radius `T` lies in
`Finset.Icc (-⌊n * T⌋) ⌊n * T⌋`. -/
theorem floor_trace_mem_Icc (h : Scaffold b σ φ K₀ K₁) {T : ℝ} {x : R}
    (hx : ∀ i, |σ i x| ≤ T) :
    ⌊trace σ x⌋ ∈ Finset.Icc (-⌊(Fintype.card ι : ℝ) * T⌋) ⌊(Fintype.card ι : ℝ) * T⌋ := by
  obtain ⟨z, hz⟩ := h.trace_int x
  have hz' : trace σ x = z := hz
  have habs := abs_trace_le σ hx
  rw [hz', abs_le] at habs
  rw [hz', Int.floor_intCast, Finset.mem_Icc]
  constructor
  · rw [neg_le]
    exact Int.le_floor.mpr (by push_cast; linarith [habs.1])
  · exact Int.le_floor.mpr habs.2

/-- Blueprint C01: the trace fiber. Under `Scaffold` with `K₀ > 0`, for every real `T ≥ 1` there is
an integer `s` and a `Finset` `A ⊆ boxFinset T` on which the trace is constantly `s`, with
`(T / (n * K₀)) ^ n / ((2 * n + 1) * T) ≤ #A`. -/
theorem exists_trace_fiber (h : Scaffold b σ φ K₀ K₁) (hK₀ : 0 < K₀) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (s : ℤ) (A : Finset R), A ⊆ h.boxFinset T ∧ (∀ a ∈ A, trace σ a = s) ∧
      (T / (Fintype.card ι * K₀)) ^ Fintype.card ι / ((2 * Fintype.card ι + 1) * T) ≤
        (A.card : ℝ) := by
  classical
  set n := Fintype.card ι with hn
  set N : ℤ := ⌊(n : ℝ) * T⌋ with hN
  set t : Finset ℤ := Finset.Icc (-N) N with ht
  set s : Finset R := h.boxFinset T with hs
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr (by positivity)
  -- the size of the target set
  have ht_card : (t.card : ℝ) = 2 * (N : ℝ) + 1 := by
    have := Int.card_Icc_of_le (a := -N) (b := N) (by omega)
    have h' : ((t.card : ℤ) : ℝ) = ((N + 1 - -N : ℤ) : ℝ) := by rw [ht, this]
    push_cast at h'
    linarith
  have ht_pos : (0 : ℝ) < t.card := by rw [ht_card]; positivity
  have ht_le : (t.card : ℝ) ≤ (2 * n + 1) * T := by
    rw [ht_card]
    have := Int.floor_le ((n : ℝ) * T)
    rw [← hN] at this
    nlinarith
  have ht_ne : t.Nonempty := ⟨0, by rw [ht, Finset.mem_Icc]; omega⟩
  -- the floor of the trace maps the box into `t`
  have hmaps : ∀ a ∈ s, ⌊trace σ a⌋ ∈ t := fun a ha ↦
    h.floor_trace_mem_Icc ((h.mem_boxFinset).mp ha)
  -- pigeonhole
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := (s.card : ℝ) / t.card) hmaps ht_ne
    (by rw [nsmul_eq_mul, mul_div_cancel₀ _ ht_pos.ne'])
  refine ⟨y, s.filter (fun a ↦ ⌊trace σ a⌋ = y), Finset.filter_subset _ _, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨z, hz⟩ := h.trace_int a
    have hz' : trace σ a = z := hz
    rw [hz', Int.floor_intCast] at ha
    rw [hz', ha.2]
  · refine le_trans ?_ hy
    have hbox := h.le_card_boxFinset hK₀ hT0
    rw [← hn, ← hs] at hbox
    exact div_le_div₀ (Nat.cast_nonneg _) hbox (by positivity) ht_le

end TraceFiber

end Scaffold

end Nikodym
