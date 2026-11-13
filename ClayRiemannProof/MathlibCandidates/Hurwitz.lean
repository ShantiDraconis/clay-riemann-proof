/-
Copyright (c) 2026 Tiago Paschoalatto Fagliari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiago Paschoalatto Fagliari
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Hurwitz's theorem: zeros persist under uniform limits

Candidate for Mathlib. Mathlib has the holomorphy of locally uniform limits
(`TendstoLocallyUniformlyOn.differentiableOn`) but not Hurwitz's theorem on their zeros.

## Main results

* `Complex.eventually_exists_zero_of_tendstoUniformlyOn`: if holomorphic functions `F i` converge uniformly
  to `f` on a closed ball, `f` vanishes at the centre and has no zero on the boundary sphere, then eventually
  every `F i` has a zero in the closed ball.
* `Complex.im_eq_zero_of_tendstoLocallyUniformly`: a locally uniform limit of entire functions with only real
  zeros has only real zeros, at every zero where it is not locally zero.

The proof of the first applies the maximum modulus principle to `1 / F i`.
-/

open Filter Metric Topology

namespace Complex

/-- **Hurwitz's theorem**, existence of zeros. If the functions `F i` are holomorphic on `closedBall z₀ r`
and converge uniformly to `f` there, `f` is continuous on the sphere, `f z₀ = 0`, and `f` has no zero on
`sphere z₀ r`, then eventually every `F i` has a zero in `closedBall z₀ r`. -/
theorem eventually_exists_zero_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hF : ∀ i, DifferentiableOn ℂ (F i) (closedBall z₀ r))
    (hconv : TendstoUniformlyOn F f l (closedBall z₀ r)) (hfc : ContinuousOn f (sphere z₀ r))
    (hf0 : f z₀ = 0) (hfs : ∀ z ∈ sphere z₀ r, f z ≠ 0) :
    ∀ᶠ i in l, ∃ w ∈ closedBall z₀ r, F i w = 0 := by
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hfc.norm
  have hm0 : 0 < ‖f z₁‖ := norm_pos_iff.mpr (hfs z₁ hz₁)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (‖f z₁‖ / 2) (by positivity)] with i hi
  by_contra hne
  push Not at hne
  have hd : DiffContOnCl ℂ (fun z => (F i z)⁻¹) (ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact (hF i).inv hne
  have hC : ∀ z ∈ frontier (ball z₀ r), ‖(fun z => (F i z)⁻¹) z‖ ≤ (‖f z₁‖ / 2)⁻¹ := by
    intro z hz
    rw [frontier_ball z₀ hr.ne'] at hz
    have h1 : ‖f z₁‖ ≤ ‖f z‖ := isMinOn_iff.mp hmin z hz
    have h2 : dist (f z) (F i z) < ‖f z₁‖ / 2 := hi z (sphere_subset_closedBall hz)
    rw [dist_eq_norm] at h2
    have h3 : ‖f z₁‖ / 2 ≤ ‖F i z‖ := by
      have := norm_sub_norm_le (f z) (F i z)
      linarith
    simp only [norm_inv]
    exact inv_anti₀ (by positivity) h3
  have hρ := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hC
    (subset_closure (mem_ball_self hr))
  have h4 : dist (f z₀) (F i z₀) < ‖f z₁‖ / 2 := hi z₀ (mem_closedBall_self hr.le)
  rw [hf0, dist_zero_left] at h4
  simp only [norm_inv] at hρ
  have h5 : 0 < ‖F i z₀‖ := norm_pos_iff.mpr (hne z₀ (mem_closedBall_self hr.le))
  have := (inv_le_inv₀ h5 (by positivity)).mp hρ
  linarith

/-- **Hurwitz's theorem**, real zeros. If entire functions `G n` have only real zeros and converge locally
uniformly to `g`, then every zero of `g` at which `g` is not locally zero is real. -/
theorem im_eq_zero_of_tendstoLocallyUniformly {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hG : ∀ n, Differentiable ℂ (G n)) (hA : ∀ n z, G n z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformly G g atTop) {z : ℂ} (hz : g z = 0)
    (hnz : ¬ ∀ᶠ w in 𝓝 z, g w = 0) : z.im = 0 := by
  have hconv' : TendstoLocallyUniformlyOn G g atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have hgd : DifferentiableOn ℂ g Set.univ :=
    hconv'.differentiableOn (Eventually.of_forall fun n => (hG n).differentiableOn) isOpen_univ
  have hiso : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    ((hgd.analyticAt Filter.univ_mem).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  rw [eventually_nhdsWithin_iff] at hiso
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp hiso
  have key : ∀ r : ℝ, 0 < r → r < r₀ → |z.im| ≤ r := by
    intro r hr hrr
    have hev := eventually_exists_zero_of_tendstoUniformlyOn hr (fun n => (hG n).differentiableOn)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hconv' _ (Set.subset_univ _)
        (isCompact_closedBall z r))
      (hgd.continuousOn.mono (Set.subset_univ _)) hz
      (fun w hw => by
        have hd : dist w z = r := Metric.mem_sphere.mp hw
        refine hball (by rw [hd]; exact hrr) ?_
        intro h
        rw [h, dist_self] at hd
        exact hr.ne hd)
    obtain ⟨n, w, hw, hw0⟩ := hev.exists
    have hwim := hA n w hw0
    have hdist : dist w z ≤ r := Metric.mem_closedBall.mp hw
    rw [dist_eq_norm] at hdist
    have := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im, hwim, zero_sub, abs_neg] at this
    linarith
  by_contra hne
  have hd : 0 < |z.im| := abs_pos.mpr hne
  have h := key (min (|z.im| / 2) (r₀ / 2)) (by positivity)
    (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have := min_le_left (|z.im| / 2) (r₀ / 2)
  linarith

end Complex

#print axioms Complex.eventually_exists_zero_of_tendstoUniformlyOn
#print axioms Complex.im_eq_zero_of_tendstoLocallyUniformly
