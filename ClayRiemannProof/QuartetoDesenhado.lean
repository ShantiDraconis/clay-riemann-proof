import ClayRiemannProof.CertifiedZeros.Evaluation

/-!
# O quarteto desenhado em `0,3 ± 14i`, `0,7 ± 14i` não existe (kernel)

Um quarteto fora da reta na altura 14 (`b = ±0,2`, os pontos `0,3 ± 14i` e `0,7 ± 14i`) é refutado pelo kernel com a
avaliação certificada de `ζ` (`CertifiedZeros.Evaluation`: Euler–Maclaurin com `N = 8`, `M = 8`, retângulo
racional verificado por `decide +kernel`): nos quatro pontos `|ζ| ≥ 1/10`. O valor de `|ζ|` ali é cerca de 0,175
(em `0,7 ± 14i`) e 0,205 (em `0,3 ± 14i`); o zero mais próximo é `½ + 14,1347…i`, na reta.

Nada aqui prova ou refuta RH; é a refutação de quatro pontos específicos. `OPEN_MATH = true`.
-/

open Complex

namespace ClayRiemannProof.QuartetoDesenhado

open ClayRiemannProof.CertifiedZeros.Evaluation

set_option maxRecDepth 100000 in
/-- `|ζ(7/10 + 14i)| ≥ 1/10`. -/
theorem cota_07_mais : ((1 / 10 : ℚ) : ℝ) ≤ ‖riemannZeta ((((7 / 10 : ℚ) : ℝ) : ℂ) + (((14 : ℚ) : ℝ) : ℂ) * I)‖ :=
  le_norm_de (mem_zetaIG (N := 8) (M := 8) (K := 16) (nT := 24) (p := 32) (by norm_num) (by norm_num)
    (by norm_num) (σ := 7 / 10) (by norm_num) 14 (by norm_num) (by decide +kernel)) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `|ζ(3/10 + 14i)| ≥ 1/10`. -/
theorem cota_03_mais : ((1 / 10 : ℚ) : ℝ) ≤ ‖riemannZeta ((((3 / 10 : ℚ) : ℝ) : ℂ) + (((14 : ℚ) : ℝ) : ℂ) * I)‖ :=
  le_norm_de (mem_zetaIG (N := 8) (M := 8) (K := 16) (nT := 24) (p := 32) (by norm_num) (by norm_num)
    (by norm_num) (σ := 3 / 10) (by norm_num) 14 (by norm_num) (by decide +kernel)) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `|ζ(7/10 − 14i)| ≥ 1/10`. -/
theorem cota_07_menos :
    ((1 / 10 : ℚ) : ℝ) ≤ ‖riemannZeta ((((7 / 10 : ℚ) : ℝ) : ℂ) + (((-14 : ℚ) : ℝ) : ℂ) * I)‖ :=
  le_norm_de (mem_zetaIG (N := 8) (M := 8) (K := 16) (nT := 24) (p := 32) (by norm_num) (by norm_num)
    (by norm_num) (σ := 7 / 10) (by norm_num) (-14) (by norm_num) (by decide +kernel)) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `|ζ(3/10 − 14i)| ≥ 1/10`. -/
theorem cota_03_menos :
    ((1 / 10 : ℚ) : ℝ) ≤ ‖riemannZeta ((((3 / 10 : ℚ) : ℝ) : ℂ) + (((-14 : ℚ) : ℝ) : ℂ) * I)‖ :=
  le_norm_de (mem_zetaIG (N := 8) (M := 8) (K := 16) (nT := 24) (p := 32) (by norm_num) (by norm_num)
    (by norm_num) (σ := 3 / 10) (by norm_num) (-14) (by norm_num) (by decide +kernel)) (by norm_num)
    (by decide +kernel)

/-- Norma `≥ v > 0` ⟹ não é zero. -/
theorem nao_zero_de_cota {z : ℂ} {v : ℝ} (hv : 0 < v) (h : v ≤ ‖riemannZeta z‖) : riemannZeta z ≠ 0 := by
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- **O quarteto `0,3 ± 14i`, `0,7 ± 14i` não é de zeros de `ζ`.** -/
theorem quarteto_desenhado :
    riemannZeta (7 / 10 + 14 * I) ≠ 0 ∧ riemannZeta (3 / 10 + 14 * I) ≠ 0 ∧
      riemannZeta (7 / 10 - 14 * I) ≠ 0 ∧ riemannZeta (3 / 10 - 14 * I) ≠ 0 := by
  have hv : (0 : ℝ) < ((1 / 10 : ℚ) : ℝ) := by norm_num
  have e1 : (7 / 10 + 14 * I : ℂ) = (((7 / 10 : ℚ) : ℝ) : ℂ) + (((14 : ℚ) : ℝ) : ℂ) * I := by
    first
      | (push_cast; ring)
      | push_cast
      | norm_num
  have e2 : (3 / 10 + 14 * I : ℂ) = (((3 / 10 : ℚ) : ℝ) : ℂ) + (((14 : ℚ) : ℝ) : ℂ) * I := by
    first
      | (push_cast; ring)
      | push_cast
      | norm_num
  have e3 : (7 / 10 - 14 * I : ℂ) = (((7 / 10 : ℚ) : ℝ) : ℂ) + (((-14 : ℚ) : ℝ) : ℂ) * I := by
    first
      | (push_cast; ring)
      | push_cast
      | norm_num
  have e4 : (3 / 10 - 14 * I : ℂ) = (((3 / 10 : ℚ) : ℝ) : ℂ) + (((-14 : ℚ) : ℝ) : ℂ) * I := by
    first
      | (push_cast; ring)
      | push_cast
      | norm_num
  rw [e1, e2, e3, e4]
  exact ⟨nao_zero_de_cota hv cota_07_mais, nao_zero_de_cota hv cota_03_mais,
    nao_zero_de_cota hv cota_07_menos, nao_zero_de_cota hv cota_03_menos⟩

end ClayRiemannProof.QuartetoDesenhado
