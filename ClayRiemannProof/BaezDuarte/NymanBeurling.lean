import ClayRiemannProof.BaezDuarte.MellinRho

/-!
# Transformada de Mellin das funções de Nyman–Beurling `f_θ`

Generaliza `MellinRho` do parâmetro discreto `θ = 1/k` (Báez-Duarte) para todo `θ > 0` real
(Nyman 1950, Beurling 1955). Para `0 < Re s < 1`:

* `mellin_rhoθ`: `∫_0^∞ {θ/t} t^{s−1} dt = −θ^s ζ(s)/s` (para `θ = 1/k` é `MellinRho.mellin_rho`);
* `fθ θ t = {θ/t} − θ {1/t}` se anula para `t > 1` quando `0 < θ ≤ 1` (`fθ_eq_zero_of_one_lt`):
  é uma função de `L²(0,1)`, a família cujo fecho linear denso em `L²(0,1)` equivale a RH;
* `mellin_fθ`: `∫_0^∞ f_θ(t) t^{s−1} dt = (θ − θ^s) ζ(s)/s`, e a mesma integral em `(0,1]`
  (`integral_Ioc_fθ`), que é a identidade de Nyman–Beurling;
* `integral_Ioc_fθ_eq_zero`: se `ζ(s) = 0` na faixa, `∫_0^1 f_θ(t) t^{s−1} dt = 0` para todo `θ ∈ (0,1]`.

Nada aqui prova RH: são as identidades exatas que ligam a família `f_θ` aos zeros de `ζ`.
-/

open Complex Set MeasureTheory

namespace ClayRiemannProof.BaezDuarte.NymanBeurling

open ClayRiemannProof.Zeta.Strip ClayRiemannProof.BaezDuarte.MellinRho

/-- `t ↦ {θ/t}` como função complexa. -/
noncomputable def rhoθ (θ : ℝ) (t : ℝ) : ℂ := fr (θ / t)

/-- A função de Nyman–Beurling `f_θ(t) = {θ/t} − θ {1/t}`. -/
noncomputable def fθ (θ : ℝ) (t : ℝ) : ℂ := rhoθ θ t - (θ : ℂ) * rhoθ 1 t

theorem rhoθ_eq_comp (θ : ℝ) :
    rhoθ θ = fun t => (fun u : ℝ => fr u⁻¹) (θ⁻¹ * t) := by
  funext t
  show fr (θ / t) = fr (θ⁻¹ * t)⁻¹
  rw [mul_inv, inv_inv, div_eq_mul_inv]

theorem cpow_inv_neg {θ : ℝ} (hθ : 0 < θ) (s : ℂ) : ((θ⁻¹ : ℝ) : ℂ) ^ (-s) = (θ : ℂ) ^ s := by
  rw [ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hθ.le]; exact
    Real.pi_ne_zero.symm), Complex.cpow_neg, inv_inv]

/-- Convergência e valor da transformada de Mellin de `{θ/t}` na faixa `0 < Re s < 1`. -/
theorem mellin_rhoθ_aux {θ : ℝ} (hθ : 0 < θ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (rhoθ θ) s ∧ mellin (rhoθ θ) s = (θ : ℂ) ^ s * (1 / (1 - s) + H s) := by
  have hθ' : (0 : ℝ) < θ⁻¹ := inv_pos.mpr hθ
  obtain ⟨hc, hm⟩ := mellin_fr_neg hs0 hs1
  have hinv : (fun u : ℝ => fr u⁻¹) = fun u => fr (u ^ (-1 : ℝ)) := by
    funext u; rw [Real.rpow_neg_one]
  constructor
  · rw [rhoθ_eq_comp]
    refine (MellinConvergent.comp_mul_left (f := fun u : ℝ => fr u⁻¹) hθ').mpr ?_
    rw [hinv]
    refine (MellinConvergent.comp_rpow (f := fr) (by norm_num : (-1 : ℝ) ≠ 0)).mpr ?_
    have hs' : s / (((-1 : ℝ)) : ℂ) = -s := by push_cast; ring
    rw [hs']
    exact hc
  · calc mellin (rhoθ θ) s
        = mellin (fun t => (fun u : ℝ => fr u⁻¹) (θ⁻¹ * t)) s := by rw [rhoθ_eq_comp]
      _ = ((θ⁻¹ : ℝ) : ℂ) ^ (-s) • mellin (fun u : ℝ => fr u⁻¹) s :=
          mellin_comp_mul_left (fun u : ℝ => fr u⁻¹) s hθ'
      _ = ((θ⁻¹ : ℝ) : ℂ) ^ (-s) * mellin fr (-s) := by rw [mellin_comp_inv, smul_eq_mul]
      _ = (θ : ℂ) ^ s * (1 / (1 - s) + H s) := by rw [hm, cpow_inv_neg hθ]

theorem mellinConvergent_rhoθ {θ : ℝ} (hθ : 0 < θ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (rhoθ θ) s :=
  (mellin_rhoθ_aux hθ hs0 hs1).1

/-- **`∫_0^∞ {θ/t} t^{s−1} dt = −θ^s ζ(s)/s`** para `θ > 0` e `0 < Re s < 1`. -/
theorem mellin_rhoθ {θ : ℝ} (hθ : 0 < θ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (rhoθ θ) s = -((θ : ℂ) ^ s * riemannZeta s / s) := by
  have hsne : s ≠ 1 := by intro h; rw [h, one_re] at hs1; exact lt_irrefl 1 hs1
  have hs0' : s ≠ 0 := by intro h; rw [h, zero_re] at hs0; exact lt_irrefl 0 hs0
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  rw [(mellin_rhoθ_aux hθ hs0 hs1).2, H_eq_zeta hs0 hsne]
  field_simp
  ring

/-- Para `0 < θ ≤ 1`, `f_θ` se anula em `(1, ∞)`: `{θ/t} = θ/t` e `{1/t} = 1/t`. -/
theorem fθ_eq_zero_of_one_lt {θ t : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht : 1 < t) : fθ θ t = 0 := by
  have ht0 : 0 < t := lt_trans one_pos ht
  have h1 : Int.fract (θ / t) = θ / t :=
    Int.fract_eq_self.mpr ⟨(div_pos hθ0 ht0).le, (div_lt_one ht0).mpr (lt_of_le_of_lt hθ1 ht)⟩
  have h2 : Int.fract (1 / t) = 1 / t :=
    Int.fract_eq_self.mpr ⟨(div_pos one_pos ht0).le, (div_lt_one ht0).mpr ht⟩
  unfold fθ rhoθ fr
  rw [h1, h2]
  push_cast
  ring

/-- `f_θ = {θ/·} + (−θ)•{1/·}` (forma usada para a linearidade da transformada de Mellin). -/
theorem fθ_eq (θ : ℝ) : fθ θ = fun t => rhoθ θ t + (-(θ : ℂ)) • rhoθ 1 t := by
  funext t
  unfold fθ
  rw [smul_eq_mul, neg_mul, ← sub_eq_add_neg]

theorem mellinConvergent_fθ {θ : ℝ} (hθ : 0 < θ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fθ θ) s := by
  rw [fθ_eq]
  exact (hasMellin_add (mellinConvergent_rhoθ hθ hs0 hs1)
    ((mellinConvergent_rhoθ one_pos hs0 hs1).const_smul (-(θ : ℂ)))).1

/-- **Identidade de Nyman–Beurling**: `∫_0^∞ f_θ(t) t^{s−1} dt = (θ − θ^s) ζ(s)/s` para `θ > 0`,
`0 < Re s < 1`. -/
theorem mellin_fθ {θ : ℝ} (hθ : 0 < θ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fθ θ) s = ((θ : ℂ) - (θ : ℂ) ^ s) * riemannZeta s / s := by
  rw [fθ_eq, (hasMellin_add (mellinConvergent_rhoθ hθ hs0 hs1)
    ((mellinConvergent_rhoθ one_pos hs0 hs1).const_smul (-(θ : ℂ)))).2,
    mellin_const_smul (rhoθ 1) s (-(θ : ℂ)), mellin_rhoθ hθ hs0 hs1, mellin_rhoθ one_pos hs0 hs1, smul_eq_mul,
    ofReal_one, one_cpow]
  ring

/-- A transformada de Mellin de `f_θ` (`0 < θ ≤ 1`) é a integral em `(0,1]`: `f_θ = 0` em `(1,∞)`. -/
theorem mellin_fθ_eq_integral_Ioc {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (s : ℂ) :
    mellin (fθ θ) s = ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • fθ θ t := by
  unfold mellin
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (fun t ht => ht.1) ?_
  intro t ht
  have h1 : 1 < t := by
    rcases ht with ⟨ht0, htn⟩
    by_contra h
    exact htn ⟨ht0, not_lt.mp h⟩
  rw [fθ_eq_zero_of_one_lt hθ0 hθ1 h1, smul_zero]

/-- **`∫_0^1 f_θ(t) t^{s−1} dt = (θ − θ^s) ζ(s)/s`** para `0 < θ ≤ 1`, `0 < Re s < 1`. -/
theorem integral_Ioc_fθ {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • fθ θ t = ((θ : ℂ) - (θ : ℂ) ^ s) * riemannZeta s / s := by
  rw [← mellin_fθ_eq_integral_Ioc hθ0 hθ1, mellin_fθ hθ0 hs0 hs1]

/-- Se `ζ(s) = 0` com `0 < Re s < 1`, então `∫_0^1 f_θ(t) t^{s−1} dt = 0` para todo `θ ∈ (0,1]`. -/
theorem integral_Ioc_fθ_eq_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) (hz : riemannZeta s = 0) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • fθ θ t = 0 := by
  rw [integral_Ioc_fθ hθ0 hθ1 hs0 hs1, hz]
  simp

end ClayRiemannProof.BaezDuarte.NymanBeurling
