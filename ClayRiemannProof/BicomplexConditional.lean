import ClayRiemannProof.Zeta.Symmetry

/-!
# Conditional component bridge (supplementary)

This module formalizes a precise conditional statement about the two idempotent
coordinates of a bicomplex parameter. It does not define a bicomplex analytic
continuation of zeta and does not prove the Riemann Hypothesis.
-/

namespace ClayRiemannProof.BicomplexConditional

/-- The two ordinary complex coordinates associated with σ + t i + b k. -/
def componentPlus (sigma t b : ℝ) : ℂ := ⟨sigma + b, t⟩
def componentMinus (sigma t b : ℝ) : ℂ := ⟨sigma - b, t⟩

/-- The ordinary zeta zero predicate restricted to the open critical strip. -/
def ZetaZeroInStrip (z : ℂ) : Prop :=
  riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1

/-- If RH holds for both ordinary component zeros, both component real parts
are 1/2; the coordinate equations then force σ=1/2 and b=0. -/
theorem both_components_RH_force_center
    (sigma t b : ℝ)
    (hRH : ∀ z : ℂ, ZetaZeroInStrip z → z.re = 1 / 2)
    (hPlus : riemannZeta (componentPlus sigma t b) = 0)
    (hPlusLo : 0 < sigma + b) (hPlusHi : sigma + b < 1)
    (hMinus : riemannZeta (componentMinus sigma t b) = 0)
    (hMinusLo : 0 < sigma - b) (hMinusHi : sigma - b < 1) :
    sigma = 1 / 2 ∧ b = 0 := by
  have hp : (componentPlus sigma t b).re = 1 / 2 :=
    hRH _ ⟨hPlus, by simpa [componentPlus] using hPlusLo,
      by simpa [componentPlus] using hPlusHi⟩
  have hm : (componentMinus sigma t b).re = 1 / 2 :=
    hRH _ ⟨hMinus, by simpa [componentMinus] using hMinusLo,
      by simpa [componentMinus] using hMinusHi⟩
  have hp' : sigma + b = 1 / 2 := by simpa [componentPlus] using hp
  have hm' : sigma - b = 1 / 2 := by simpa [componentMinus] using hm
  constructor <;> linarith

/-- One component equation alone does not determine b: this is a coordinate
counterexample, not a claim that the selected point is a zeta zero. -/
theorem one_component_does_not_force_b_zero :
    ∃ sigma b : ℝ, sigma + b = 1 / 2 ∧ b ≠ 0 := by
  exact ⟨1 / 4, 1 / 4, by norm_num, by norm_num⟩

/-- If both component real coordinates are 1/2, the bicomplex coordinates
are centered: σ=1/2 and b=0. -/
theorem component_coordinates_force_center (sigma b : ℝ)
    (hPlus : sigma + b = 1 / 2) (hMinus : sigma - b = 1 / 2) :
    sigma = 1 / 2 ∧ b = 0 := by
  constructor <;> linarith

end ClayRiemannProof.BicomplexConditional
