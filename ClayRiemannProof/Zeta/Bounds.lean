import ClayRiemannProof.Zeta.Strip

/-!
# ζ na faixa: a cota `|ζ(s)| ≤ |s|/|s−1| + |s|/(2 Re s)` para `Re s > 0`

Origem: ATK kernel (espelho público), `ATK/ZetaRetangulo.lean` (`Hr`, `norm_H_le`, `Hr_le`) e
`ATK/ZetaRegiao.lean` (`zeta_eq`, `norm_zeta_le`). Só o fecho mínimo necessário para a recíproca
de Báez-Duarte foi portado (as regiões sem zeros desses arquivos não são usadas aqui).

* `norm_H_le`, `Hr_le`: `|∫_1^∞ {t} t^{-s-1} dt| ≤ ∫_1^∞ {t} t^{-σ-1} dt ≤ 1/(2σ)` (`σ = Re s > 0`);
* `norm_zeta_le`: `|ζ(s)| ≤ |s|/|s−1| + |s|/(2 Re s)` para `Re s > 0`, `s ≠ 1`.
-/

open Complex Set MeasureTheory Filter Topology

namespace ClayRiemannProof.Zeta.Bounds

open ClayRiemannProof.Zeta.Strip

/-- `∫_1^∞ {t} t^{-σ-1} dt`. -/
noncomputable def Hr (σ : ℝ) : ℝ := ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) * Int.fract t

/-- `({t} − 1/2) t^{-σ-1}`. -/
noncomputable def g (σ t : ℝ) : ℝ := (Int.fract t - 1 / 2) * t ^ (-σ - 1)

theorem norm_H_le {s : ℂ} : ‖H s‖ ≤ Hr s.re := by
  rw [H_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  unfold Hr
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg t), show (-s - 1).re = -s.re - 1 by simp]

theorem integrableOn_rpow {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

theorem integrableOn_g {σ : ℝ} (hσ : 0 < σ) : IntegrableOn (g σ) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_rpow hσ).const_mul (1 / 2)) ?_ ?_
  · exact (((measurable_fract : Measurable (Int.fract : ℝ → ℝ)).sub_const _).mul
      ((measurable_id : Measurable (fun t : ℝ => t)).pow_const (-σ - 1))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans zero_lt_one ht)
    unfold g
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0 _)]
    have h1 : |Int.fract t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0 _)

theorem integral_rpow {σ : ℝ} (hσ : 0 < σ) : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow,
    show -σ - 1 + 1 = -σ by ring]
  field_simp

theorem Hr_eq {σ : ℝ} (hσ : 0 < σ) : Hr σ = (∫ t in Ioi (1 : ℝ), g σ t) + 1 / (2 * σ) := by
  have e : (fun t : ℝ => t ^ (-σ - 1) * Int.fract t) =
      fun t => g σ t + 1 / 2 * t ^ (-σ - 1) := by
    funext t; unfold g; ring
  unfold Hr
  rw [e, integral_add (integrableOn_g hσ) ((integrableOn_rpow hσ).const_mul _),
    integral_const_mul, integral_rpow hσ]
  field_simp

theorem fract_on {m : ℕ} {t : ℝ} (h1 : (m : ℝ) ≤ t) (h2 : t < m + 1) : Int.fract t = t - m := by
  have hf : ⌊t⌋ = (m : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast h1, by push_cast; exact h2⟩
  unfold Int.fract
  rw [hf]
  push_cast
  ring

theorem intervalIntegrable_g {σ : ℝ} (hσ : 0 < σ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (g σ) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_g hσ).mono_set fun t ht => lt_of_le_of_lt ha ht.1

/-- Em cada intervalo unitário `[m, m+1]`, `m ≥ 1`: `∫ ({t} − 1/2) t^{-σ-1} ≤ 0`. -/
theorem peca_nonpos {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m) :
    ∫ t in (m : ℝ)..(m + 1), g σ t ≤ 0 := by
  set c : ℝ := ((m : ℝ) + 1 / 2) ^ (-σ - 1) with hc
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hint := intervalIntegrable_g hσ hm0 (by linarith : (m : ℝ) ≤ m + 1)
  have hint2 : IntervalIntegrable (fun t : ℝ => (t - (m + 1 / 2)) * c) volume (m : ℝ) (m + 1) :=
    ((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable _ _
  have hpt : ∀ t ∈ Ioo (m : ℝ) (m + 1), g σ t ≤ (t - (m + 1 / 2)) * c := by
    rintro t ⟨h1, h2⟩
    have ht0 : 0 < t := by linarith
    unfold g
    rw [fract_on h1.le h2, show t - m - 1 / 2 = t - (m + 1 / 2) by ring]
    rcases le_total t ((m : ℝ) + 1 / 2) with h | h
    · have hpow : c ≤ t ^ (-σ - 1) := Real.rpow_le_rpow_of_nonpos ht0 h (by linarith)
      exact mul_le_mul_of_nonpos_left hpow (by linarith)
    · have hpow : t ^ (-σ - 1) ≤ c := Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
      exact mul_le_mul_of_nonneg_left hpow (by linarith)
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) hint hint2 hpt
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const]
  have h0 : ∫ t in (m : ℝ)..(m + 1), (t - (m + 1 / 2)) = 0 := by
    rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x), integral_id]
    ring
  rw [h0, zero_mul]

/-- `∫_1^∞ ({t} − 1/2) t^{-σ-1} dt ≤ 0`. -/
theorem integral_g_nonpos {σ : ℝ} (hσ : 0 < σ) : ∫ t in Ioi (1 : ℝ), g σ t ≤ 0 := by
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop)
    (b := fun n : ℕ => (n : ℝ) + 1) 1 (integrableOn_g hσ)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlim fun n => ?_
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := g σ) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) + 1) (n := n) fun k _ =>
      intervalIntegrable_g hσ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (by push_cast; linarith)
  simp only [Nat.cast_zero, zero_add] at hsum
  rw [← hsum]
  refine Finset.sum_nonpos fun k _ => ?_
  have := peca_nonpos hσ (m := k + 1) (by omega)
  convert this using 2
  push_cast
  ring

/-- **`∫_1^∞ {t} t^{-σ-1} dt ≤ 1/(2σ)`.** -/
theorem Hr_le {σ : ℝ} (hσ : 0 < σ) : Hr σ ≤ 1 / (2 * σ) := by
  rw [Hr_eq hσ]; linarith [integral_g_nonpos hσ]

theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * H s := by
  have h := H_eq_zeta hs hs1
  have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_re] at hs; exact lt_irrefl 0 hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [h]
  field_simp
  ring

/-- `|ζ(s)| ≤ |s|/|s−1| + |s|/(2 Re s)`. -/
theorem norm_zeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / (2 * s.re) := by
  rw [zeta_eq hs hs1]
  calc ‖s / (s - 1) - s * H s‖ ≤ ‖s / (s - 1)‖ + ‖s * H s‖ := norm_sub_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / (2 * s.re)) := by
        rw [norm_div, norm_mul]
        gcongr
        exact (norm_H_le (s := s)).trans (Hr_le hs)
    _ = _ := by ring

end ClayRiemannProof.Zeta.Bounds
