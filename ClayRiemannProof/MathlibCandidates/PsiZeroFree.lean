/-
Copyright (c) 2026 Tiago Paschoalatto Fagliari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiago Paschoalatto Fagliari
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# A power-saving error term for `ψ` gives a zero-free half-plane for `ζ`

Candidate for Mathlib. If `ψ x - x = O(x ^ β)` with `0 ≤ β`, then `riemannZeta s ≠ 0` for
`β < s.re`.

## Main results

* `Chebyshev.riemannZeta_ne_zero_of_isBigO`: the statement above.

## Proof

With `E n = Λ n - 1`, Abel summation (`LSeries_eq_mul_integral`) gives
`-ζ'/ζ - ζ = F` on `1 < re s`, where `F s = s * mellin R (-s)` and `R t = ψ t - ⌊t⌋` for `1 < t`.
The hypothesis makes `F` holomorphic on `β < re s` (`mellin_differentiableAt_of_isBigO_rpow`).
Hence `ζ' + ζ (ζ + F) = 0` on the connected open set `{β < re s} \ {1}`. At a zero `ρ` of order
`n + 1`, writing `ζ = (s - ρ) ^ (n + 1) g` with `g ρ ≠ 0`, this identity becomes
`(s - ρ) ^ n * ((n + 1) g + (s - ρ) (g' + g (ζ + F))) = 0` near `ρ`, which is impossible since the
second factor is `(n + 1) g ρ ≠ 0` at `ρ`.
-/

open Filter Topology Asymptotics MeasureTheory

namespace Chebyshev

/-- `Λ n - 1`, whose partial sums are `ψ n - n`. -/
private noncomputable def err (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) - 1

private lemma sum_err (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, err k = ((psi n - n : ℝ) : ℂ) := by
  have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    constructor <;> intro h <;> omega
  rw [psi, Nat.floor_natCast, hI]
  push_cast
  simp [err, Finset.sum_sub_distrib]

private lemma isBigO_sum_err {β : ℝ} (h : (fun x : ℝ ↦ psi x - x) =O[atTop] fun x ↦ x ^ β) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, err k) =O[atTop] fun n ↦ (n : ℝ) ^ β := by
  refine isBigO_norm_left.mp ((isBigO_norm_left.mpr h.natCast_atTop).congr_left fun n ↦ ?_)
  rw [sum_err, Complex.norm_real]

private lemma LSeries_err {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable err s ∧
      LSeries err s = -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
  have h1 : LSeriesSummable (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h2 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have he : err = (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) - 1 := rfl
  rw [he]
  refine ⟨h1.sub h2, ?_⟩
  rw [LSeries_sub h1 h2, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_one_eq_riemannZeta hs]

/-- `ψ t - ⌊t⌋` for `1 < t`, and `0` otherwise. -/
private noncomputable def rem : ℝ → ℂ :=
  Set.indicator (Set.Ioi 1) fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, err k

private lemma measurable_rem : Measurable rem := by
  have h : Measurable fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, err k :=
    (measurable_from_nat (f := fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, err k)).comp Nat.measurable_floor
  exact h.indicator measurableSet_Ioi

private lemma locallyIntegrableOn_rem : LocallyIntegrableOn rem (Set.Ioi 0) := by
  refine LocallyIntegrable.locallyIntegrableOn ?_ _
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.bddAbove
  refine Measure.integrableOn_of_bounded
    (M := ∑ n ∈ Finset.range (⌊R⌋₊ + 1), ‖∑ k ∈ Finset.Icc 1 n, err k‖)
    hK.measure_lt_top.ne measurable_rem.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  by_cases h1 : t ∈ Set.Ioi (1 : ℝ)
  · rw [rem, Set.indicator_of_mem h1]
    exact Finset.single_le_sum (f := fun n ↦ ‖∑ k ∈ Finset.Icc 1 n, err k‖)
      (fun n _ ↦ norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (hR ht))))
  · rw [rem, Set.indicator_of_notMem h1, norm_zero]
    exact Finset.sum_nonneg fun n _ ↦ norm_nonneg _

private lemma isBigO_rem_atTop {β : ℝ} (hβ : 0 ≤ β)
    (h : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, err k) =O[atTop] fun n ↦ (n : ℝ) ^ β) :
    rem =O[atTop] fun t : ℝ ↦ t ^ β := by
  have hreal : (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, err k) =O[atTop] fun t ↦ t ^ β :=
    (h.comp_tendsto tendsto_nat_floor_atTop).trans <|
      isEquivalent_nat_floor.isBigO.rpow hβ (eventually_ge_atTop 0)
  refine EventuallyEq.trans_isBigO ?_ hreal
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [rem, Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from ht)]

private lemma isBigO_rem_zero (b : ℝ) : rem =O[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ (-b) := by
  refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
  rw [rem, Set.indicator_of_notMem
    (show t ∉ Set.Ioi (1 : ℝ) from fun h1 ↦ lt_asymm (Set.mem_Iio.mp ht) (Set.mem_Ioi.mp h1))]

private lemma integral_eq_mellin_rem (s : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, err k) * (t : ℂ) ^ (-(s + 1))
      = mellin rem (-s) := by
  have h : mellin rem (-s) = ∫ t in Set.Ioi (0 : ℝ),
      (Set.Ioi (1 : ℝ)).indicator
        (fun t : ℝ ↦ (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, err k) * (t : ℂ) ^ (-(s + 1))) t := by
    unfold mellin
    congr 1
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simp only [rem, Set.indicator_of_mem ht, smul_eq_mul]
      rw [show -s - 1 = -(s + 1) by ring]
      ring
    · simp only [rem, Set.indicator_of_notMem ht, smul_zero]
  rw [h, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi zero_le_one)]

/-- `s * mellin R (-s)`, the continuation of `-ζ'(s)/ζ(s) - ζ(s)`. -/
private noncomputable def remMellin (s : ℂ) : ℂ := s * mellin rem (-s)

private lemma differentiableAt_remMellin {β : ℝ} (hβ : 0 ≤ β)
    (h : (fun x : ℝ ↦ psi x - x) =O[atTop] fun x ↦ x ^ β) {s : ℂ} (hs : β < s.re) :
    DifferentiableAt ℂ remMellin s := by
  have hm : DifferentiableAt ℂ (mellin rem) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -β) (b := -s.re - 1) locallyIntegrableOn_rem
      (by simpa only [neg_neg] using isBigO_rem_atTop hβ (isBigO_sum_err h))
      (by rw [Complex.neg_re]; linarith) (isBigO_rem_zero _) (by rw [Complex.neg_re]; linarith)
  have hneg : DifferentiableAt ℂ (fun z : ℂ ↦ -z) s := differentiableAt_id.neg
  show DifferentiableAt ℂ (fun z : ℂ ↦ z * mellin rem (-z)) s
  exact differentiableAt_id.mul (hm.comp s hneg)

/-- On `1 < re s`, `-ζ'(s)/ζ(s) - ζ(s) = s * mellin R (-s)`. -/
private lemma neg_logDeriv_sub_eq {β : ℝ} (hβ : 0 ≤ β)
    (h : (fun x : ℝ ↦ psi x - x) =O[atTop] fun x ↦ x ^ β) {s : ℂ} (hs : 1 < s.re)
    (hβs : β < s.re) :
    -deriv riemannZeta s / riemannZeta s - riemannZeta s = remMellin s := by
  obtain ⟨hsum, heq⟩ := LSeries_err hs
  rw [← heq, LSeries_eq_mul_integral err hβ hβs hsum (isBigO_sum_err h), integral_eq_mellin_rem]
  rfl

/-- `{s | β < re s} \ {1}` is preconnected for `β < 1`. -/
private lemma isPreconnected_re_gt_inter_compl_one {β : ℝ} (hβ : β < 1) :
    IsPreconnected ({s : ℂ | β < s.re} ∩ {1}ᶜ) := by
  have hA : IsPreconnected ({s : ℂ | β < s.re} ∩ {s | 0 < s.im}) :=
    ((convex_halfSpace_re_gt β).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected ({s : ℂ | β < s.re} ∩ {s | s.im < 0}) :=
    ((convex_halfSpace_re_gt β).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hC : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hD : IsPreconnected ({s : ℂ | β < s.re} ∩ {s | s.re < 1}) :=
    ((convex_halfSpace_re_gt β).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hU : {s : ℂ | β < s.re} ∩ {1}ᶜ =
      ((({s : ℂ | β < s.re} ∩ {s | 0 < s.im}) ∪ {s | 1 < s.re}) ∪
        ({s : ℂ | β < s.re} ∩ {s | s.im < 0})) ∪ ({s : ℂ | β < s.re} ∩ {s | s.re < 1}) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy s.im 0 with hi | hi | hi
      · exact Or.inl (Or.inr ⟨h1, hi⟩)
      · rcases lt_trichotomy s.re 1 with hr | hr | hr
        · exact Or.inr ⟨h1, hr⟩
        · exact absurd (Complex.ext (z := s) (w := 1) (by simpa using hr) (by simpa using hi)) h2
        · exact Or.inl (Or.inl (Or.inr hr))
      · exact Or.inl (Or.inl (Or.inl ⟨h1, hi⟩))
    · rintro (((⟨h1, hi⟩ | hr) | ⟨h1, hi⟩) | ⟨h1, hr⟩)
      · exact ⟨h1, fun h ↦ by rw [h] at hi; simp at hi⟩
      · exact ⟨by linarith, fun h ↦ by rw [h] at hr; simp at hr⟩
      · exact ⟨h1, fun h ↦ by rw [h] at hi; simp at hi⟩
      · exact ⟨h1, fun h ↦ by rw [h] at hr; simp at hr⟩
  rw [hU]
  have p1 : (⟨2, 1⟩ : ℂ) ∈ {s : ℂ | β < s.re} ∩ {s | 0 < s.im} :=
    Set.mem_inter (show β < 2 by linarith) (show (0 : ℝ) < 1 by norm_num)
  have p2 : (⟨2, 1⟩ : ℂ) ∈ {s : ℂ | 1 < s.re} := show (1 : ℝ) < 2 by norm_num
  have p3 : (⟨2, -1⟩ : ℂ) ∈ {s : ℂ | 1 < s.re} := show (1 : ℝ) < 2 by norm_num
  have p4 : (⟨2, -1⟩ : ℂ) ∈ {s : ℂ | β < s.re} ∩ {s | s.im < 0} :=
    Set.mem_inter (show β < 2 by linarith) (show (-1 : ℝ) < 0 by norm_num)
  have p5 : (⟨(β + 1) / 2, 1⟩ : ℂ) ∈ {s : ℂ | β < s.re} ∩ {s | 0 < s.im} :=
    Set.mem_inter (show β < (β + 1) / 2 by linarith) (show (0 : ℝ) < 1 by norm_num)
  have p6 : (⟨(β + 1) / 2, 1⟩ : ℂ) ∈ {s : ℂ | β < s.re} ∩ {s | s.re < 1} :=
    Set.mem_inter (show β < (β + 1) / 2 by linarith) (show (β + 1) / 2 < 1 by linarith)
  have hAC := IsPreconnected.union _ p1 p2 hA hC
  have hACB := IsPreconnected.union _ (Set.mem_union_right _ p3) p4 hAC hB
  exact IsPreconnected.union _ (Set.mem_union_left _ (Set.mem_union_left _ p5)) p6 hACB hD

/-- **Power saving in the prime number theorem gives a zero-free half-plane.** If
`ψ x - x = O(x ^ β)` with `0 ≤ β`, then `ζ` has no zeros with `β < re s`. -/
theorem riemannZeta_ne_zero_of_isBigO {β : ℝ} (hβ : 0 ≤ β)
    (h : (fun x : ℝ ↦ psi x - x) =O[atTop] fun x ↦ x ^ β) {ρ : ℂ} (hρ : β < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  have hFd : ∀ {s : ℂ}, β < s.re → DifferentiableAt ℂ remMellin s :=
    fun hs ↦ differentiableAt_remMellin hβ h hs
  intro hz
  have hρ1 : ρ.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
  have hβ1 : β < 1 := hρ.trans hρ1
  have hρne : ρ ≠ 1 := by
    rintro rfl
    simp at hρ1
  have hρc : ρ ∈ ({1}ᶜ : Set ℂ) := Set.mem_compl_singleton_iff.mpr hρne
  have h2c : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := Set.mem_compl_singleton_iff.mpr (by norm_num)
  have hζ2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  -- `ζ' + ζ (ζ + remMellin) = 0` on `{β < re s} \ {1}`
  have hFan : AnalyticOnNhd ℂ remMellin {s : ℂ | β < s.re} :=
    DifferentiableOn.analyticOnNhd (fun s hs ↦ (hFd hs).differentiableWithinAt)
      (isOpen_lt continuous_const Complex.continuous_re)
  have hHan : AnalyticOnNhd ℂ
      (fun s ↦ deriv riemannZeta s + riemannZeta s * (riemannZeta s + remMellin s))
      ({s : ℂ | β < s.re} ∩ {1}ᶜ) := by
    intro s hs
    have a1 : AnalyticAt ℂ (deriv riemannZeta) s := analyticOn_riemannZeta.deriv s hs.2
    have a2 : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs.2
    have a3 : AnalyticAt ℂ remMellin s := hFan s hs.1
    exact a1.add (a2.mul (a2.add a3))
  have h2U : (2 : ℂ) ∈ {s : ℂ | β < s.re} ∩ {1}ᶜ :=
    ⟨show β < (2 : ℂ).re by rw [Complex.re_ofNat]; linarith, h2c⟩
  have hH2 : (fun s ↦ deriv riemannZeta s + riemannZeta s * (riemannZeta s + remMellin s))
      =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by rw [Complex.re_ofNat]; norm_num)
    filter_upwards [hmem] with s hs
    have hs' : 1 < s.re := hs
    have hne := riemannZeta_ne_zero_of_one_le_re hs'.le
    have hid := neg_logDeriv_sub_eq hβ h hs' (by linarith)
    have h1 : -deriv riemannZeta s / riemannZeta s = riemannZeta s + remMellin s := by
      linear_combination hid
    rw [div_eq_iff hne] at h1
    show deriv riemannZeta s + riemannZeta s * (riemannZeta s + remMellin s) = 0
    linear_combination -h1
  have hEq := hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_re_gt_inter_compl_one hβ1) h2U hH2
  have hUo : IsOpen ({s : ℂ | β < s.re} ∩ {1}ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hρU : ρ ∈ {s : ℂ | β < s.re} ∩ {1}ᶜ := ⟨hρ, hρc⟩
  have hHρ : ∀ᶠ z in 𝓝 ρ,
      deriv riemannZeta z + riemannZeta z * (riemannZeta z + remMellin z) = 0 := by
    filter_upwards [hUo.mem_nhds hρU] with z hz
    exact hEq hz
  -- `ζ` is not identically zero near `ρ`
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, riemannZeta z = 0 := by
    intro hev
    exact hζ2 (analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected hρc hev h2c)
  obtain ⟨n, g, hg, hgρ, hev⟩ :=
    (analyticOn_riemannZeta ρ hρc).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hnot
  cases n with
  | zero =>
    have h0 := hev.self_of_nhds
    rw [hz, pow_zero, one_smul] at h0
    exact hgρ h0.symm
  | succ m =>
    have hev' : ∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ (m + 1) * g z :=
      hev.mono fun z hz' ↦ by rw [hz', smul_eq_mul]
    have hevd : deriv riemannZeta =ᶠ[𝓝 ρ] deriv (fun z ↦ (z - ρ) ^ (m + 1) * g z) :=
      Filter.EventuallyEq.deriv hev'
    have hdP : ∀ z, AnalyticAt ℂ g z →
        deriv (fun w ↦ (w - ρ) ^ (m + 1) * g w) z
          = ((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * g z + (z - ρ) ^ (m + 1) * deriv g z := by
      intro z hgz
      have hsub : HasDerivAt (fun w : ℂ ↦ w - ρ) 1 z :=
        (hasDerivAt_sub_const_iff ρ).mpr (hasDerivAt_id' (x := z))
      have hpow := hsub.pow (m + 1)
      rw [Nat.add_sub_cancel, mul_one] at hpow
      have hprod : HasDerivAt (fun w ↦ (w - ρ) ^ (m + 1) * g w)
          (((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * g z + (z - ρ) ^ (m + 1) * deriv g z) z :=
        hpow.mul hgz.differentiableAt.hasDerivAt
      exact hprod.deriv
    have hkc : ContinuousAt (fun z ↦ ((m + 1 : ℕ) : ℂ) * g z
        + (z - ρ) * (deriv g z + g z * (riemannZeta z + remMellin z))) ρ := by
      have c1 : ContinuousAt g ρ := hg.continuousAt
      have c2 : ContinuousAt (deriv g) ρ := hg.deriv.continuousAt
      have c3 : ContinuousAt riemannZeta ρ := (differentiableAt_riemannZeta hρne).continuousAt
      have c4 : ContinuousAt remMellin ρ := (hFd hρ).continuousAt
      exact (continuousAt_const.mul c1).add
        ((continuousAt_id.sub continuousAt_const).mul (c2.add (c1.mul (c3.add c4))))
    have hk0 : ((m + 1 : ℕ) : ℂ) * g ρ
        + (ρ - ρ) * (deriv g ρ + g ρ * (riemannZeta ρ + remMellin ρ)) ≠ 0 := by
      rw [sub_self, zero_mul, add_zero]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)) hgρ
    have hall : ∀ᶠ z in 𝓝 ρ, (z - ρ) ^ m = 0 := by
      filter_upwards [hHρ, hev', hevd, hg.eventually_analyticAt, hkc.eventually_ne hk0]
        with z hH hzz hdz hgz hkz
      have hd := hdP z hgz
      have hkey : (z - ρ) ^ m * (((m + 1 : ℕ) : ℂ) * g z
          + (z - ρ) * (deriv g z + g z * (riemannZeta z + remMellin z))) = 0 := by
        linear_combination hH - hdz - hd - (riemannZeta z + remMellin z) * hzz
      exact (mul_eq_zero.mp hkey).resolve_right hkz
    obtain ⟨z, hz0, hzne⟩ := ((hall.filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := {ρ}ᶜ) (a := ρ))).exists
    exact pow_ne_zero m (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hzne)) hz0

end Chebyshev

/-- info: 'Chebyshev.riemannZeta_ne_zero_of_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chebyshev.riemannZeta_ne_zero_of_isBigO
