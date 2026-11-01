import ClayRiemannProof.Zeta.Symmetry

/-!
# Centered spectral dictionary (supplementary)

This module records the exact coordinate change between a zeta zero ρ and
the centered parameter λ = ρ - 1/2. It formalizes a geometric equivalence,
not an identification with a physical system or an RH proof.
-/

namespace ClayRiemannProof.CenteredStabilityBridge

open ClayRiemannProof.Zeta.Symmetry

/-- Shift the critical line Re(s)=1/2 to the imaginary axis. -/
noncomputable def centered (s : ℂ) : ℂ := s - (1 / 2 : ℂ)

/-- The real coordinate after centering is Re(s)-1/2. -/
theorem re_centered (s : ℂ) : (centered s).re = s.re - 1 / 2 := by
  simp [centered]

/-- A point is on the critical line exactly when its centered real part is zero. -/
theorem centered_on_axis_iff (s : ℂ) :
    (centered s).re = 0 ↔ s.re = 1 / 2 := by
  rw [re_centered]
  constructor <;> intro h <;> linarith

/-- The functional-equation reflection s ↦ 1-s becomes λ ↦ -λ after centering. -/
theorem centered_reflection (s : ℂ) :
    centered (1 - s) = -centered s := by
  simp [centered]
  ring

/-- The RH statement for nontrivial zeros is exactly neutrality on the
centered axis. This is an equivalence, not a proof of either side. -/
theorem riemann_iff_centered_neutral :
    RiemannHypothesis ↔ ∀ s ∈ Z, (centered s).re = 0 := by
  rw [riemann_iff_torcao]
  constructor
  · intro h s hs
    have hline : s.re = 1 / 2 := (torcao_fixo_iff s).mp (h s hs)
    rw [re_centered, hline]
    norm_num
  · intro h s hs
    apply (torcao_fixo_iff s).mpr
    have hcenter := h s hs
    rw [re_centered] at hcenter
    linarith

/-- A hypothetical quartet centered at 1/2 has real offsets ±δ. -/
theorem hypothetical_rectangle_real_parts (delta gamma : ℝ) :
    (centered ⟨1 / 2 + delta, gamma⟩).re = delta ∧
    (centered ⟨1 / 2 - delta, gamma⟩).re = -delta ∧
    (centered ⟨1 / 2 + delta, -gamma⟩).re = delta ∧
    (centered ⟨1 / 2 - delta, -gamma⟩).re = -delta := by
  simp [centered]

end ClayRiemannProof.CenteredStabilityBridge
